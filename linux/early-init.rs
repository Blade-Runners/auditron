use std::env;
use std::ffi::OsStr;
use std::fs::{self, File, OpenOptions};
use std::io::{self, Write};
use std::os::unix::fs::{MetadataExt, PermissionsExt};
use std::os::unix::process::CommandExt;
use std::path::{Path, PathBuf};
use std::process::{Command, Stdio};
use std::time::{SystemTime, UNIX_EPOCH};

const REPORT_DIR: &str = "/run/auditron";
const REPORT_JSON: &str = "/run/auditron/report.json";
const DEFS: &str = "/usr/local/lib/auditron/definitions.json";
const BOOTHASH: &str = "/var/lib/auditron/boothash";
const VERSION: &str = "2.0.0-rust";

#[derive(Clone, Debug)]
enum Json {
    Null,
    Bool(bool),
    Number(String),
    String(String),
    Array(Vec<Json>),
    Object(Vec<(String, Json)>),
}

impl Json {
    fn object(&self, key: &str) -> Option<&Json> {
        match self {
            Json::Object(items) => items.iter().find(|(k, _)| k == key).map(|(_, v)| v),
            _ => None,
        }
    }
    fn string(&self) -> Option<&str> {
        match self { Json::String(s) => Some(s), _ => None }
    }
    fn array(&self) -> Option<&[Json]> {
        match self { Json::Array(a) => Some(a), _ => None }
    }
}

struct Parser<'a> { s: &'a [u8], p: usize }
impl<'a> Parser<'a> {
    fn new(s: &'a str) -> Self { Self { s: s.as_bytes(), p: 0 } }
    fn parse(mut self) -> Result<Json, String> {
        self.ws();
        let v = self.value()?;
        self.ws();
        if self.p != self.s.len() { return Err(format!("trailing JSON at byte {}", self.p)); }
        Ok(v)
    }
    fn ws(&mut self) { while self.p < self.s.len() && matches!(self.s[self.p], b' ' | b'\n' | b'\r' | b'\t') { self.p += 1; } }
    fn value(&mut self) -> Result<Json, String> {
        self.ws();
        if self.p >= self.s.len() { return Err("unexpected end of JSON".into()); }
        match self.s[self.p] {
            b'n' => { self.expect(b"null")?; Ok(Json::Null) }
            b't' => { self.expect(b"true")?; Ok(Json::Bool(true)) }
            b'f' => { self.expect(b"false")?; Ok(Json::Bool(false)) }
            b'"' => Ok(Json::String(self.string()?)),
            b'[' => self.array(),
            b'{' => self.object(),
            b'-' | b'0'..=b'9' => self.number(),
            _ => Err(format!("unexpected byte {} at {}", self.s[self.p], self.p)),
        }
    }
    fn expect(&mut self, want: &[u8]) -> Result<(), String> {
        if self.s.get(self.p..self.p + want.len()) == Some(want) { self.p += want.len(); Ok(()) }
        else { Err(format!("invalid token at {}", self.p)) }
    }
    fn string(&mut self) -> Result<String, String> {
        if self.s.get(self.p) != Some(&b'"') { return Err("expected string".into()); }
        self.p += 1;
        let mut out = String::new();
        while self.p < self.s.len() {
            let b = self.s[self.p]; self.p += 1;
            match b {
                b'"' => return Ok(out),
                b'\\' => {
                    if self.p >= self.s.len() { return Err("unterminated escape".into()); }
                    let e = self.s[self.p]; self.p += 1;
                    match e {
                        b'"' => out.push('"'), b'\\' => out.push('\\'), b'/' => out.push('/'),
                        b'b' => out.push('\u{0008}'), b'f' => out.push('\u{000c}'),
                        b'n' => out.push('\n'), b'r' => out.push('\r'), b't' => out.push('\t'),
                        b'u' => {
                            let cp = self.hex4()?;
                            if (0xD800..=0xDBFF).contains(&cp) {
                                if self.s.get(self.p..self.p + 2) != Some(b"\\u") { return Err("unpaired UTF-16 surrogate".into()); }
                                self.p += 2;
                                let low = self.hex4()?;
                                if !(0xDC00..=0xDFFF).contains(&low) { return Err("invalid low surrogate".into()); }
                                let full = 0x10000 + ((cp - 0xD800) << 10) + (low - 0xDC00);
                                out.push(char::from_u32(full).ok_or("invalid codepoint")?);
                            } else if (0xDC00..=0xDFFF).contains(&cp) {
                                return Err("unpaired low surrogate".into());
                            } else { out.push(char::from_u32(cp).ok_or("invalid codepoint")?); }
                        }
                        _ => return Err("invalid escape".into()),
                    }
                }
                0x00..=0x1f => return Err("control character in string".into()),
                _ => {
                    let start = self.p - 1;
                    while self.p < self.s.len() && self.s[self.p] >= 0x20 && self.s[self.p] != b'"' && self.s[self.p] != b'\\' { self.p += 1; }
                    out.push_str(std::str::from_utf8(&self.s[start..self.p]).map_err(|_| "invalid UTF-8")?);
                }
            }
        }
        Err("unterminated string".into())
    }
    fn hex4(&mut self) -> Result<u32, String> {
        if self.p + 4 > self.s.len() { return Err("short unicode escape".into()); }
        let mut n = 0u32;
        for _ in 0..4 {
            n = (n << 4) | match self.s[self.p] {
                b'0'..=b'9' => (self.s[self.p] - b'0') as u32,
                b'a'..=b'f' => (self.s[self.p] - b'a' + 10) as u32,
                b'A'..=b'F' => (self.s[self.p] - b'A' + 10) as u32,
                _ => return Err("invalid unicode escape".into()),
            }; self.p += 1;
        }
        Ok(n)
    }
    fn array(&mut self) -> Result<Json, String> {
        self.p += 1; self.ws(); let mut a = Vec::new();
        if self.s.get(self.p) == Some(&b']') { self.p += 1; return Ok(Json::Array(a)); }
        loop {
            a.push(self.value()?); self.ws();
            match self.s.get(self.p) { Some(b',') => { self.p += 1; }, Some(b']') => { self.p += 1; break; }, _ => return Err(format!("expected , or ] at {}", self.p)) }
        }
        Ok(Json::Array(a))
    }
    fn object(&mut self) -> Result<Json, String> {
        self.p += 1; self.ws(); let mut o = Vec::new();
        if self.s.get(self.p) == Some(&b'}') { self.p += 1; return Ok(Json::Object(o)); }
        loop {
            self.ws(); let k = self.string()?; self.ws();
            if self.s.get(self.p) != Some(&b':') { return Err(format!("expected : at {}", self.p)); }
            self.p += 1; let v = self.value()?; o.push((k, v)); self.ws();
            match self.s.get(self.p) { Some(b',') => { self.p += 1; }, Some(b'}') => { self.p += 1; break; }, _ => return Err(format!("expected , or }} at {}", self.p)) }
        }
        Ok(Json::Object(o))
    }
    fn number(&mut self) -> Result<Json, String> {
        let start = self.p;
        if self.s[self.p] == b'-' { self.p += 1; }
        if self.p >= self.s.len() { return Err("bad number".into()); }
        if self.s[self.p] == b'0' { self.p += 1; }
        else if self.s[self.p].is_ascii_digit() { while self.p < self.s.len() && self.s[self.p].is_ascii_digit() { self.p += 1; } }
        else { return Err("bad number".into()); }
        if self.s.get(self.p) == Some(&b'.') { self.p += 1; if !self.s.get(self.p).map_or(false, u8::is_ascii_digit) { return Err("bad number".into()); } while self.p < self.s.len() && self.s[self.p].is_ascii_digit() { self.p += 1; } }
        if matches!(self.s.get(self.p), Some(b'e') | Some(b'E')) { self.p += 1; if matches!(self.s.get(self.p), Some(b'+') | Some(b'-')) { self.p += 1; } if !self.s.get(self.p).map_or(false, u8::is_ascii_digit) { return Err("bad exponent".into()); } while self.p < self.s.len() && self.s[self.p].is_ascii_digit() { self.p += 1; } }
        Ok(Json::Number(String::from_utf8(self.s[start..self.p].to_vec()).map_err(|_| "bad number")?))
    }
}

fn json_escape(s: &str) -> String {
    let mut o = String::with_capacity(s.len() + 8);
    for c in s.chars() {
        match c { '"' => o.push_str("\\\""), '\\' => o.push_str("\\\\"), '\n' => o.push_str("\\n"), '\r' => o.push_str("\\r"), '\t' => o.push_str("\\t"), '\u{08}' => o.push_str("\\b"), '\u{0c}' => o.push_str("\\f"), c if c.is_control() => o.push_str(&format!("\\u{:04x}", c as u32)), c => o.push(c) }
    }
    o
}
fn jq_string(s: &str) -> String { format!("\"{}\"", json_escape(s)) }

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum Action { Report, Fix, Quarantine, Unknown }
fn action(s: &str) -> Action { match s { "report" => Action::Report, "fix" => Action::Fix, "quarantine" => Action::Quarantine, _ => Action::Unknown } }

#[derive(Debug)]
struct Rule<'a> {
    id: &'a str,
    desc: &'a str,
    kind: &'a str,
    path: &'a str,
    pattern: &'a str,
    action: Action,
    action_raw: &'a str,
    perm: Option<&'a str>,
}

struct Check {
    fields: Vec<(String, String)>, // already JSON encoded values
}
impl Check {
    fn new() -> Self { Self { fields: Vec::new() } }
    fn s(&mut self, k: &str, v: &str) { self.fields.push((k.into(), jq_string(v))); }
    fn b(&mut self, k: &str, v: bool) { self.fields.push((k.into(), if v { "true".into() } else { "false".into() })); }
    fn obj(&self) -> String {
        let mut s = String::from("{");
        for (i, (k,v)) in self.fields.iter().enumerate() { if i > 0 { s.push(','); } s.push_str(&jq_string(k)); s.push(':'); s.push_str(v); }
        s.push('}'); s
    }
}

fn now_iso() -> String {
    let secs = SystemTime::now().duration_since(UNIX_EPOCH).unwrap_or_default().as_secs() as i64;
    let days = secs.div_euclid(86_400); let sod = secs.rem_euclid(86_400);
    let (y,m,d) = civil_from_days(days);
    format!("{:04}-{:02}-{:02}T{:02}:{:02}:{:02}Z", y,m,d,sod/3600,(sod%3600)/60,sod%60)
}
fn civil_from_days(z: i64) -> (i64,i64,i64) {
    let z = z + 719468; let era = if z >= 0 { z } else { z - 146096 } / 146097; let doe = z - era * 146097;
    let yoe = (doe - doe/1460 + doe/36524 - doe/146096) / 365; let y = yoe + era*400;
    let doy = doe - (365*yoe + yoe/4 - yoe/100); let mp = (5*doy+2)/153; let d = doy - (153*mp+2)/5 + 1; let m = mp + if mp < 10 {3} else {-9};
    (y + if m <= 2 {1} else {0}, m, d)
}

fn log(msg: &str) {
    eprintln!("[auditron] {}", msg);
    if let Ok(mut f) = OpenOptions::new().write(true).open("/dev/kmsg") { let _ = writeln!(f, "<6>[auditron] {}", msg); }
}

fn mkdir_p(p: &Path) -> io::Result<()> { fs::create_dir_all(p) }

fn mount_if_needed(source: &str, target: &str, fstype: &str) {
    if Path::new(target).is_dir() {
        let status = Command::new("mount").args(["-t", fstype, source, target]).stdin(Stdio::null()).stdout(Stdio::null()).stderr(Stdio::null()).status();
        match status { Ok(s) if s.success() => log(&format!("mounted {}", target)), _ => {} }
    }
}

fn safe_walk(root: &Path, recursive: bool, out: &mut Vec<PathBuf>) -> io::Result<()> {
    let mut stack = vec![root.to_path_buf()];
    while let Some(dir) = stack.pop() {
        let rd = match fs::read_dir(&dir) { Ok(r) => r, Err(e) => { log(&format!("cannot read {}: {}", dir.display(), e)); continue; } };
        for ent in rd {
            let ent = match ent { Ok(e) => e, Err(_) => continue };
            let p = ent.path(); let ft = match ent.file_type() { Ok(x) => x, Err(_) => continue };
            if ft.is_file() { out.push(p); }
            else if recursive && ft.is_dir() { stack.push(p); }
        }
    }
    Ok(())
}

fn basename(p: &Path) -> &str { p.file_name().and_then(OsStr::to_str).unwrap_or("") }
fn glob_match(pat: &str, text: &str) -> bool {
    let p: Vec<char> = pat.chars().collect(); let t: Vec<char> = text.chars().collect();
    let (mut i, mut j, mut star, mut mark) = (0usize,0usize,None,None);
    while j < t.len() {
        if i < p.len() && (p[i] == '?' || p[i] == t[j]) { i+=1; j+=1; }
        else if i < p.len() && p[i] == '*' { star=Some(i); mark=Some(j); i+=1; }
        else if let Some(s) = star { i=s+1; let m=mark.unwrap()+1; mark=Some(m); j=m; }
        else { return false; }
    }
    while i < p.len() && p[i] == '*' { i+=1; }
    i == p.len()
}

fn find_matches(base: &Path, pattern: &str) -> Vec<PathBuf> {
    let leading = pattern.starts_with('/');
    let pat = pattern.trim_start_matches('/');
    let recursive = !leading;
    let mut files = Vec::new();
    let _ = safe_walk(base, recursive, &mut files);
    files.into_iter().filter(|p| {
        if leading { glob_match(pat, basename(p)) } else { glob_match(pat, basename(p)) }
    }).collect()
}

fn parse_perm(s: &str) -> Option<(u32,u32,u32)> {
    let mut it=s.split(':'); let uid=it.next()?.parse().ok()?; let gid=it.next()?.parse().ok()?;
    let mode_s=it.next()?; if it.next().is_some() { return None; }
    let mode=u32::from_str_radix(mode_s,8).ok()?; Some((uid,gid,mode))
}

fn apply_fix(path: &Path, kind: &str, perm: Option<&str>) -> Result<String,String> {
    match kind {
        "permission" => {
            let (uid,gid,mode)=parse_perm(perm.ok_or("missing perm")?).ok_or("invalid perm")?;
            let owner = format!("{}:{}",uid,gid);
            let c = Command::new("chown").arg(&owner).arg(path).stdin(Stdio::null()).stdout(Stdio::null()).stderr(Stdio::null()).status().map_err(|e| e.to_string())?;
            if !c.success() { return Err(format!("chown failed: {}", c)); }
            let c = Command::new("chmod").arg(format!("{:04o}",mode)).arg(path).stdin(Stdio::null()).stdout(Stdio::null()).stderr(Stdio::null()).status().map_err(|e| e.to_string())?;
            if !c.success() { return Err(format!("chmod failed: {}", c)); }
            Ok("fixed".into())
        }
        "suid" => chmod_special(path, "u-s"),
        "sgid" => chmod_special(path, "g-s"),
        _ => Err("unsupported fix type".into()),
    }
}
fn chmod_special(path: &Path, arg: &str) -> Result<String,String> {
    let c=Command::new("chmod").arg(arg).arg(path).stdin(Stdio::null()).stdout(Stdio::null()).stderr(Stdio::null()).status().map_err(|e|e.to_string())?;
    if c.success() { Ok("fixed".into()) } else { Err(format!("chmod failed: {}",c)) }
}
fn quarantine(path: &Path) -> Result<String,String> {
    let qdir=Path::new("/run/auditron/quarantine"); mkdir_p(qdir).map_err(|e|e.to_string())?;
    let name=basename(path); let stamp=SystemTime::now().duration_since(UNIX_EPOCH).unwrap_or_default().as_nanos();
    let dest=qdir.join(format!("{}.{}", stamp, name));
    fs::rename(path,&dest).map_err(|e|e.to_string())?;
    Ok(dest.display().to_string())
}

fn check_rule(rule: &Rule, checks: &mut Vec<Check>) {
    if !rule.path.starts_with('/') || rule.path.contains("..") { 
        let mut c=Check::new(); c.s("id",rule.id); c.s("description",rule.desc); c.s("status","ERROR"); c.s("action",rule.action_raw); c.s("error","unsafe rule path"); checks.push(c); return;
    }
    let matches=find_matches(Path::new(rule.path), rule.pattern);
    for p in matches {
        let md=match fs::symlink_metadata(&p) { Ok(x)=>x, Err(_)=>continue };
        let violation=match rule.kind {
            "file" => true,
            "permission" => match (md.uid(),md.gid(),md.permissions().mode() & 0o7777, rule.perm.and_then(parse_perm)) { (u,g,m,Some((ru,rg,rm))) => u!=ru || g!=rg || m!=rm, _ => true },
            "suid" => md.permissions().mode() & 0o4000 != 0,
            "sgid" => md.permissions().mode() & 0o2000 != 0,
            _ => false,
        };
        if !violation { continue; }
        let mut c=Check::new(); c.s("id",rule.id); c.s("description",rule.desc); c.s("status","FOUND"); c.s("path",&p.display().to_string()); c.s("action",rule.action_raw);
        match rule.action {
            Action::Report => c.s("action_result","reported"),
            Action::Fix => match apply_fix(&p,rule.kind,rule.perm) { Ok(r)=>c.s("action_result",&r), Err(e)=>{c.s("action_result","ERROR");c.s("error",&e);} },
            Action::Quarantine => match quarantine(&p) { Ok(dest)=>{c.s("action_result","quarantined");c.s("quarantine_path",&dest);}, Err(e)=>{c.s("action_result","ERROR");c.s("error",&e);} },
            Action::Unknown => { c.s("action_result","ERROR"); c.s("error","unknown action"); }
        }
        checks.push(c);
    }
}

fn write_report(started: &str, checks: &[Check]) -> io::Result<()> {
    mkdir_p(Path::new(REPORT_DIR))?;
    let tmp=Path::new(REPORT_DIR).join("report.json.tmp"); let mut f=File::create(&tmp)?;
    write!(f,"{{\"started\":{},\"version\":{},\"checks\":[",jq_string(started),jq_string(VERSION))?;
    for (i,c) in checks.iter().enumerate() { if i>0 { f.write_all(b",")?; } f.write_all(c.obj().as_bytes())?; }
    f.write_all(b"]}\n")?; f.sync_all()?; fs::rename(tmp,REPORT_JSON)?; Ok(())
}

fn boot_hash() {
    let root=Path::new("/boot"); if !root.is_dir() { log("/boot unavailable in initramfs; skipping boot hash"); return; }
    let mut files=Vec::new(); let _=safe_walk(root,true,&mut files); files.sort();
    let sha256=match Command::new("sha256sum").args(files.iter().map(|p|p.as_os_str())).output() { Ok(o) if o.status.success()=>o.stdout, _=>{log("sha256sum unavailable; skipping boot hash");return;} };
    let mut lines=String::from_utf8_lossy(&sha256).lines().map(str::to_owned).collect::<Vec<_>>(); lines.sort();
    let input=lines.join("\n")+"\n";
    let out=match Command::new("sha512sum").stdin(Stdio::piped()).stdout(Stdio::piped()).spawn() { Ok(mut c)=>{ if let Some(mut stdin)=c.stdin.take(){let _=stdin.write_all(input.as_bytes());} c.wait_with_output() }, Err(e)=>{log(&format!("sha512sum unavailable: {}",e));return;} };
    match out { Ok(o) if o.status.success()=>{let _=mkdir_p(Path::new("/var/lib/auditron")); let _=fs::write(BOOTHASH,o.stdout);}, _=>log("boot hash failed") }
}

fn main() {
    let args: Vec<String>=env::args().collect();
    log(&format!("starting {} at {}",VERSION,now_iso()));
    mount_if_needed("proc","/proc","proc"); mount_if_needed("sysfs","/sys","sysfs"); mount_if_needed("devtmpfs","/dev","devtmpfs");
    if let Err(e)=mkdir_p(Path::new(REPORT_DIR)) { log(&format!("cannot create report dir: {}",e)); }

    let started=now_iso(); let mut checks=Vec::new();
    boot_hash();
    match fs::read_to_string(DEFS) {
        Ok(raw)=>match Parser::new(&raw).parse() {
            Ok(root)=>{
                if let Some(rules)=root.object("rules").and_then(Json::array) {
                    for rv in rules {
                        let get=|k:&str|rv.object(k).and_then(Json::string);
                        let (Some(id),Some(desc),Some(kind),Some(path),Some(pattern),Some(act))=(get("id"),get("description"),get("type"),get("path"),get("pattern"),get("action")) else {
                            let mut c=Check::new();c.s("status","ERROR");c.s("error","malformed rule");checks.push(c);continue;
                        };
                        let r=Rule{id,desc,kind,path,pattern,action:action(act),action_raw:act,perm:get("perm")};
                        check_rule(&r,&mut checks);
                    }
                } else { let mut c=Check::new();c.s("status","ERROR");c.s("error","definitions.rules is missing or not an array");checks.push(c); }
            }
            Err(e)=>{let mut c=Check::new();c.s("status","ERROR");c.s("error",&format!("definitions parse error: {}",e));checks.push(c);}
        },
        Err(e)=>{log(&format!("definitions unavailable: {}",e)); let mut c=Check::new();c.s("status","ERROR");c.s("error","definitions unavailable in early userspace");checks.push(c);}
    }
    if let Err(e)=write_report(&started,&checks) { log(&format!("failed to write report: {}",e)); }
    log(&format!("audit complete: {} finding(s)",checks.len()));
    let init=if Path::new("/sbin/init").exists(){"/sbin/init"}else{"/bin/init"};
    let err=Command::new(init).args(args.iter().skip(1)).exec();
    log(&format!("failed to exec {}: {}",init,err));
    // Last-resort fallback: if init cannot be executed, remain alive rather than
    // returning from PID 1, which would normally panic the kernel.
    loop { std::thread::sleep(std::time::Duration::from_secs(60)); }
}
