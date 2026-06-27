// Prevent an extra console window on Windows in release builds.
#![cfg_attr(not(debug_assertions), windows_subsystem = "windows")]

use std::cmp::Reverse;
use std::collections::BinaryHeap;
use std::fs;
use std::path::Path;
use std::sync::atomic::{AtomicU8, Ordering};
use std::sync::{Arc, Mutex};
use std::time::Duration;

use serde::Serialize;
use tauri::{AppHandle, Emitter, State};
use tauri_plugin_dialog::DialogExt;
use tauri_plugin_opener::OpenerExt;

#[cfg(windows)]
use std::os::windows::fs::MetadataExt;

// ── Scan control ────────────────────────────────────────────────
// One shared byte drives the active scan: 0 = running, 1 = paused, 2 = stopped.
// A fresh Arc is created for every scan and stashed here so the pause/resume/stop
// commands (which run concurrently while `scan` is awaiting) can flip it.
struct ScanControl(Mutex<Option<Arc<AtomicU8>>>);

const RUNNING: u8 = 0;
const PAUSED: u8 = 1;
const STOPPED: u8 = 2;

// ── Payloads ────────────────────────────────────────────────────
#[derive(Clone, Serialize)]
struct Item {
    size: u64,
    path: String,
    modified: Option<i64>,
}

#[derive(Serialize)]
struct ScanResult {
    items: Vec<Item>,
    scanned: u64,
    label: String,
}

#[derive(Clone, Serialize)]
struct Progress {
    scanned: u64,
    label: &'static str,
}

#[derive(Serialize)]
struct DeleteResult {
    path: String,
    ok: bool,
    error: Option<String>,
}

#[derive(Serialize)]
struct ExportResult {
    ok: bool,
    error: Option<String>,
}

// Min-heap element: BinaryHeap is a max-heap, so we wrap items in Reverse to
// keep the *smallest* of the current top-N at the peek position for eviction.
struct HeapItem {
    size: u64,
    path: String,
    modified: Option<i64>,
}
// Eq/Ord intentionally ignore `modified` so they stay consistent with each
// other (full paths are unique, so size + path already identify an item).
impl PartialEq for HeapItem {
    fn eq(&self, other: &Self) -> bool {
        self.size == other.size && self.path == other.path
    }
}
impl Eq for HeapItem {}
impl Ord for HeapItem {
    fn cmp(&self, other: &Self) -> std::cmp::Ordering {
        self.size
            .cmp(&other.size)
            .then_with(|| self.path.cmp(&other.path))
    }
}
impl PartialOrd for HeapItem {
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        Some(self.cmp(other))
    }
}

// ── Walk state ──────────────────────────────────────────────────
struct ScanCtx {
    limit: usize,
    control: Arc<AtomicU8>,
    heap: BinaryHeap<Reverse<HeapItem>>,
    scanned: u64,
    app: AppHandle,
    label: &'static str,
}

impl ScanCtx {
    // Blocks while paused; returns false once a stop is requested.
    fn check(&self) -> bool {
        loop {
            match self.control.load(Ordering::Relaxed) {
                PAUSED => std::thread::sleep(Duration::from_millis(150)),
                STOPPED => return false,
                _ => return true,
            }
        }
    }

    // Keep only the largest `limit` items seen so far. Allocates the path
    // string only when the item actually makes the cut.
    fn maybe_insert(&mut self, size: u64, path: &Path, modified: Option<i64>) {
        if self.limit == 0 {
            return;
        }
        if self.heap.len() < self.limit {
            self.heap.push(Reverse(HeapItem {
                size,
                path: path.to_string_lossy().into_owned(),
                modified,
            }));
        } else if let Some(Reverse(min)) = self.heap.peek() {
            if size > min.size {
                self.heap.pop();
                self.heap.push(Reverse(HeapItem {
                    size,
                    path: path.to_string_lossy().into_owned(),
                    modified,
                }));
            }
        }
    }

    fn report(&self, every: u64) {
        if self.scanned % every == 0 {
            let _ = self.app.emit(
                "scan-progress",
                Progress {
                    scanned: self.scanned,
                    label: self.label,
                },
            );
        }
    }
}

// Skip symlinks and Windows junctions / reparse points so the walk can't loop
// forever through self-referential directories.
fn is_reparse(md: &fs::Metadata) -> bool {
    #[cfg(windows)]
    {
        const FILE_ATTRIBUTE_REPARSE_POINT: u32 = 0x400;
        md.file_attributes() & FILE_ATTRIBUTE_REPARSE_POINT != 0
    }
    #[cfg(not(windows))]
    {
        md.file_type().is_symlink()
    }
}

// Last-modified time as Unix epoch milliseconds, or None if unavailable.
fn mtime_millis(md: &fs::Metadata) -> Option<i64> {
    md.modified()
        .ok()
        .and_then(|t| t.duration_since(std::time::UNIX_EPOCH).ok())
        .map(|d| d.as_millis() as i64)
}

// Largest-files mode: every file competes for the top-N by its own size.
fn walk_files(ctx: &mut ScanCtx, dir: &Path) -> bool {
    if !ctx.check() {
        return false;
    }
    let entries = match fs::read_dir(dir) {
        Ok(e) => e,
        Err(_) => return true,
    };
    for entry in entries {
        if !ctx.check() {
            return false;
        }
        let entry = match entry {
            Ok(e) => e,
            Err(_) => continue,
        };
        let path = entry.path();
        let md = match fs::symlink_metadata(&path) {
            Ok(m) => m,
            Err(_) => continue,
        };
        if is_reparse(&md) {
            continue;
        }
        if md.is_dir() {
            if !walk_files(ctx, &path) {
                return false;
            }
        } else if md.is_file() {
            ctx.maybe_insert(md.len(), &path, mtime_millis(&md));
            ctx.scanned += 1;
            ctx.report(3000);
        }
    }
    true
}

// Largest-folders mode: each directory competes by its total recursive size.
// Returns (total bytes, keep-going).
fn walk_folders(ctx: &mut ScanCtx, dir: &Path, dir_modified: Option<i64>) -> (u64, bool) {
    if !ctx.check() {
        return (0, false);
    }
    let entries = match fs::read_dir(dir) {
        Ok(e) => e,
        Err(_) => return (0, true),
    };
    let mut total: u64 = 0;
    for entry in entries {
        if !ctx.check() {
            return (total, false);
        }
        let entry = match entry {
            Ok(e) => e,
            Err(_) => continue,
        };
        let path = entry.path();
        let md = match fs::symlink_metadata(&path) {
            Ok(m) => m,
            Err(_) => continue,
        };
        if is_reparse(&md) {
            continue;
        }
        if md.is_dir() {
            let (sub, keep_going) = walk_folders(ctx, &path, mtime_millis(&md));
            total += sub;
            if !keep_going {
                return (total, false);
            }
        } else if md.is_file() {
            total += md.len();
        }
    }
    ctx.scanned += 1;
    ctx.maybe_insert(total, dir, dir_modified);
    ctx.report(500);
    (total, true)
}

fn get_drives() -> Vec<String> {
    #[cfg(windows)]
    {
        let mut drives = Vec::new();
        for c in b'A'..=b'Z' {
            let root = format!("{}:\\", c as char);
            if Path::new(&root).exists() {
                drives.push(root);
            }
        }
        if drives.is_empty() {
            drives.push("C:\\".to_string());
        }
        drives
    }
    #[cfg(not(windows))]
    {
        vec!["/".to_string()]
    }
}

fn run_scan(
    app: AppHandle,
    control: Arc<AtomicU8>,
    limit: usize,
    mode: String,
    roots: Vec<String>,
) -> ScanResult {
    let folder_mode = mode == "folders";
    let label = if folder_mode { "folders" } else { "files" };
    let mut ctx = ScanCtx {
        limit,
        control,
        heap: BinaryHeap::new(),
        scanned: 0,
        app,
        label,
    };

    for drive in roots {
        if !ctx.check() {
            break;
        }
        let root = Path::new(&drive);
        if folder_mode {
            let root_mod = fs::symlink_metadata(root).ok().as_ref().and_then(mtime_millis);
            let _ = walk_folders(&mut ctx, root, root_mod);
        } else if !walk_files(&mut ctx, root) {
            break;
        }
    }

    let mut items: Vec<Item> = ctx
        .heap
        .into_vec()
        .into_iter()
        .map(|Reverse(h)| Item {
            size: h.size,
            path: h.path,
            modified: h.modified,
        })
        .collect();
    items.sort_by(|a, b| b.size.cmp(&a.size));

    ScanResult {
        items,
        scanned: ctx.scanned,
        label: label.to_string(),
    }
}

// ── Commands ────────────────────────────────────────────────────
#[tauri::command]
async fn scan(
    app: AppHandle,
    control: State<'_, ScanControl>,
    limit: usize,
    mode: String,
    root: Option<String>,
) -> Result<ScanResult, String> {
    // A specific folder narrows the scan; otherwise sweep every drive.
    let roots = match root {
        Some(r) if !r.trim().is_empty() => vec![r],
        _ => get_drives(),
    };
    let ctrl = Arc::new(AtomicU8::new(RUNNING));
    {
        *control.0.lock().unwrap() = Some(ctrl.clone());
    }
    let app2 = app.clone();
    let result =
        tauri::async_runtime::spawn_blocking(move || run_scan(app2, ctrl, limit, mode, roots))
            .await
            .map_err(|e| e.to_string())?;
    Ok(result)
}

#[tauri::command]
fn stop_scan(control: State<'_, ScanControl>) {
    if let Some(c) = control.0.lock().unwrap().as_ref() {
        c.store(STOPPED, Ordering::Relaxed);
    }
}

#[tauri::command]
fn pause_scan(control: State<'_, ScanControl>) {
    if let Some(c) = control.0.lock().unwrap().as_ref() {
        c.store(PAUSED, Ordering::Relaxed);
    }
}

#[tauri::command]
fn resume_scan(control: State<'_, ScanControl>) {
    if let Some(c) = control.0.lock().unwrap().as_ref() {
        c.store(RUNNING, Ordering::Relaxed);
    }
}

#[tauri::command]
fn delete_files(paths: Vec<String>) -> Vec<DeleteResult> {
    paths
        .into_iter()
        .map(|p| match trash::delete(&p) {
            Ok(_) => DeleteResult {
                path: p,
                ok: true,
                error: None,
            },
            Err(e) => DeleteResult {
                path: p,
                ok: false,
                error: Some(e.to_string()),
            },
        })
        .collect()
}

#[tauri::command]
fn show_in_explorer(app: AppHandle, path: String) -> Result<(), String> {
    app.opener()
        .reveal_item_in_dir(&path)
        .map_err(|e| e.to_string())
}

#[tauri::command]
fn open_external(app: AppHandle, url: String) -> Result<(), String> {
    app.opener()
        .open_url(url, None::<&str>)
        .map_err(|e| e.to_string())
}

#[tauri::command]
async fn pick_folder(app: AppHandle) -> Result<Option<String>, String> {
    let picked = tauri::async_runtime::spawn_blocking(move || {
        app.dialog().file().blocking_pick_folder()
    })
    .await
    .map_err(|e| e.to_string())?;
    Ok(picked
        .and_then(|fp| fp.into_path().ok())
        .map(|p| p.to_string_lossy().into_owned()))
}

#[tauri::command]
fn set_window_theme(window: tauri::Window, theme: String) -> Result<(), String> {
    let t = if theme == "light" {
        tauri::Theme::Light
    } else {
        tauri::Theme::Dark
    };
    window.set_theme(Some(t)).map_err(|e| e.to_string())
}

#[tauri::command]
fn copy_text(text: String) -> Result<(), String> {
    let mut clipboard = arboard::Clipboard::new().map_err(|e| e.to_string())?;
    clipboard.set_text(text).map_err(|e| e.to_string())
}

fn esc_csv(value: &str) -> String {
    format!("\"{}\"", value.replace('"', "\"\""))
}

fn build_csv(headers: &[String], rows: &[Vec<String>]) -> String {
    let mut lines: Vec<String> = Vec::with_capacity(rows.len() + 1);
    lines.push(
        headers
            .iter()
            .map(|h| esc_csv(h))
            .collect::<Vec<_>>()
            .join(","),
    );
    for row in rows {
        lines.push(row.iter().map(|c| esc_csv(c)).collect::<Vec<_>>().join(","));
    }
    lines.join("\r\n")
}

fn build_txt(headers: &[String], rows: &[Vec<String>]) -> String {
    let cols = headers.len();
    let mut widths: Vec<usize> = headers.iter().map(|h| h.chars().count()).collect();
    for row in rows {
        for (i, cell) in row.iter().enumerate().take(cols) {
            widths[i] = widths[i].max(cell.chars().count());
        }
    }
    let pad = |s: &str, w: usize| -> String {
        let mut out = String::from(s);
        for _ in s.chars().count()..w {
            out.push(' ');
        }
        out
    };
    let mut lines: Vec<String> = Vec::with_capacity(rows.len() + 2);
    lines.push(
        headers
            .iter()
            .enumerate()
            .map(|(i, h)| pad(h, widths[i]))
            .collect::<Vec<_>>()
            .join("  "),
    );
    lines.push(
        widths
            .iter()
            .map(|w| "-".repeat(*w))
            .collect::<Vec<_>>()
            .join("  "),
    );
    for row in rows {
        lines.push(
            (0..cols)
                .map(|i| pad(row.get(i).map(|s| s.as_str()).unwrap_or(""), widths[i]))
                .collect::<Vec<_>>()
                .join("  "),
        );
    }
    lines.join("\r\n")
}

#[tauri::command]
async fn export_data(
    app: AppHandle,
    format: String,
    name: String,
    headers: Vec<String>,
    rows: Vec<Vec<String>>,
) -> Result<ExportResult, String> {
    let content = if format == "csv" {
        build_csv(&headers, &rows)
    } else {
        build_txt(&headers, &rows)
    };
    let (filter_name, ext): (&str, &str) = if format == "csv" {
        ("CSV Files", "csv")
    } else {
        ("Text Files", "txt")
    };

    let app2 = app.clone();
    let picked = tauri::async_runtime::spawn_blocking(move || {
        app2.dialog()
            .file()
            .add_filter(filter_name, &[ext])
            .set_file_name(name)
            .set_title("Export Data")
            .blocking_save_file()
    })
    .await
    .map_err(|e| e.to_string())?;

    match picked {
        Some(file_path) => {
            let path = file_path.into_path().map_err(|e| e.to_string())?;
            // UTF-8 BOM so Excel reads accents correctly, matching the original.
            let mut data = String::from("\u{feff}");
            data.push_str(&content);
            match fs::write(&path, data) {
                Ok(_) => Ok(ExportResult {
                    ok: true,
                    error: None,
                }),
                Err(e) => Ok(ExportResult {
                    ok: false,
                    error: Some(e.to_string()),
                }),
            }
        }
        None => Ok(ExportResult {
            ok: false,
            error: None,
        }),
    }
}

fn main() {
    tauri::Builder::default()
        .plugin(tauri_plugin_opener::init())
        .plugin(tauri_plugin_dialog::init())
        .manage(ScanControl(Mutex::new(None)))
        .invoke_handler(tauri::generate_handler![
            scan,
            stop_scan,
            pause_scan,
            resume_scan,
            delete_files,
            show_in_explorer,
            open_external,
            pick_folder,
            set_window_theme,
            copy_text,
            export_data
        ])
        .run(tauri::generate_context!())
        .expect("error while running Size Scanner");
}
