#![allow(non_upper_case_globals)]
#![allow(non_camel_case_types)]
#![allow(non_snake_case)]
#![allow(improper_ctypes)] // Consider leaving this one on.

// TODO: Consider using a sys crate for ffi. One could be made at the moment, but it is preferable
// to find an existing well maintained one.
pub mod ffi;

use ffi::*;

#[cfg(debug_assertions)]
macro_rules! scm_validate_pair {
    ($cell:expr, $expr:expr) => {
        // The actual implementation for debug is:
        // ((!scm_is_pair (cell) ? scm_error_pair_access (cell), 0 : 0), (expr))
        $expr
    };
}

#[cfg(not(debug_assertions))]
macro_rules! scm_validate_pair {
    ($cell:expr, $expr:expr) => {
        $expr
    };
}

macro_rules! scm_pack {
    ($x:expr) => {
        $x as SCM
    };
}

macro_rules! scm_make_itag8_bits {
    ($n:expr, $tag:expr) => {
        ($n << 8) + $tag
    };
}

macro_rules! scm_makiflag_bits {
    ($n:expr) => {
        scm_make_itag8_bits!($n, scm_tc8_tags_scm_tc8_flag)
    };
}

macro_rules! scm_unpack {
    // # if defined __DECC || defined __HP_cc
    ($x:expr) => {
        $x as scm_t_bits
    }; // Figure out what to do with the other path.
}

macro_rules! scm_unpack_pointer {
    ($x:expr) => {
        scm_unpack!($x) as *mut scm_t_bits
    };
}

macro_rules! scm2ptr {
    ($x:expr) => {
        scm_unpack_pointer!($x) as *mut scm_t_cell
    };
}

macro_rules! scm_gc_cell_object {
    ($x:expr, $n:expr) => {{
        let ptr = (scm2ptr!($x) as *mut SCM).offset($n);
        *ptr
    }};
}

macro_rules! scm_cell_object {
    ($x:expr, $n:expr) => {
        scm_gc_cell_object!($x, $n)
    };
}

macro_rules! scm_cell_object_0 {
    ($x:expr) => {
        scm_cell_object!($x, 0)
    };
}

macro_rules! scm_cell_object_1 {
    ($x:expr) => {
        scm_cell_object!($x, 1)
    };
}

macro_rules! scm_car {
    ($x:expr) => {
        scm_validate_pair!($x, scm_cell_object_0!($x))
    };
}

macro_rules! scm_cdr {
    ($x:expr) => {
        scm_validate_pair!($x, scm_cell_object_1!($x))
    };
}

#[derive(Copy, Clone)]
#[repr(transparent)]
pub struct Scm(SCM);

impl Scm {
    /// Equivalent to `#t` in Scheme.
    pub const TRUE: Scm = Scm(scm_pack!(scm_makiflag_bits!(4)));

    /// Equivalent to `#f` in Scheme.
    pub const FALSE: Scm = Scm(scm_pack!(scm_makiflag_bits!(0)));

    /// Equivalent to `'()` in Scheme.
    pub const EOL: Scm = Scm(scm_pack!(scm_makiflag_bits!(3)));

    pub unsafe fn new_bool(_: bool) -> Scm {
        unimplemented!()
    }

    pub unsafe fn new_i8(x: i8) -> Scm {
        scm_from_int8(x).into()
    }

    pub unsafe fn new_u8(x: u8) -> Scm {
        scm_from_uint8(x).into()
    }

    pub unsafe fn new_i16(x: i16) -> Scm {
        scm_from_int16(x).into()
    }

    pub unsafe fn new_u16(x: u16) -> Scm {
        scm_from_uint16(x).into()
    }

    pub unsafe fn new_i32(x: i32) -> Scm {
        scm_from_int32(x).into()
    }

    pub unsafe fn new_u32(x: u32) -> Scm {
        scm_from_uint32(x).into()
    }

    pub unsafe fn new_i64(x: i64) -> Scm {
        scm_from_int64(x).into()
    }

    pub unsafe fn new_u64(x: u64) -> Scm {
        scm_from_uint64(x).into()
    }

    pub unsafe fn new_string(s: &str) -> Scm {
        scm_from_utf8_stringn(s.as_ptr() as _, s.len() as _).into()
    }

    pub unsafe fn new_symbol(s: &str) -> Scm {
        scm_from_utf8_symboln(s.as_ptr() as _, s.len() as _).into()
    }

    pub unsafe fn new_keyword(s: &str) -> Scm {
        // The Guile C API only provides a scm_from_utf8_keyword (NOT keywordn) so we have to
        // convert to a symbol. To work around this, we convert to a symbol. Note that Guile's
        // keyword implementation does the same thing anyways.
        scm_symbol_to_keyword(Self::new_symbol(s).0).into()
    }

    pub unsafe fn new_pair(x: Scm, y: Scm) -> Scm {
        Self::new_cons(x, y)
    }

    pub unsafe fn new_cons(x: Scm, y: Scm) -> Scm {
        scm_cons(x.0, y.0).into()
    }

    pub unsafe fn with_reversed_list<I: Iterator<Item = Scm>>(iter: I) -> Scm {
        let mut head = Scm::EOL;
        for x in iter {
            head = Self::new_cons(x, head);
        }
        head
    }

    pub unsafe fn with_alist<I: Iterator<Item = (Scm, Scm)>>(iter: I) -> Scm {
        let mut head = Scm::new_u8(0); // TODO: Use EOL
        for (x, y) in iter {
            head = Self::new_cons(Self::new_pair(x, y), head);
        }
        head
    }

    pub unsafe fn to_i8(&self) -> i8 {
        scm_to_int8(self.0)
    }

    pub unsafe fn to_u8(&self) -> u8 {
        scm_to_uint8(self.0)
    }

    pub unsafe fn to_i16(&self) -> i16 {
        scm_to_int16(self.0)
    }

    pub unsafe fn to_u16(&self) -> u16 {
        scm_to_uint16(self.0)
    }

    pub unsafe fn to_i32(&self) -> i32 {
        scm_to_int32(self.0)
    }

    pub unsafe fn to_u32(&self) -> u32 {
        scm_to_uint32(self.0)
    }

    pub unsafe fn to_i64(&self) -> i64 {
        scm_to_int64(self.0)
    }

    pub unsafe fn to_u64(&self) -> u64 {
        scm_to_uint64(self.0)
    }

    pub unsafe fn to_string(&self) -> String {
        let mut length = 0;
        let ptr: *mut u8 = scm_to_utf8_stringn(self.0, &mut length).cast();
        String::from_raw_parts(ptr, length as _, length as _)
    }

    pub unsafe fn to_symbol(&self) -> String {
        let s: Scm = scm_symbol_to_string(self.0).into();
        s.to_string()
    }

    pub unsafe fn to_keyword(&self) -> String {
        let s: Scm = scm_keyword_to_symbol(self.0).into();
        s.to_symbol()
    }

    pub unsafe fn car(self) -> Scm {
        scm_car!(self.0).into()
    }

    pub unsafe fn cdr(self) -> Scm {
        scm_cdr!(self.0).into()
    }
}

impl From<SCM> for Scm {
    fn from(value: SCM) -> Self {
        Scm(value)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_car() {
        unsafe {
            let a = Scm::new_i32(1);
            let b = Scm::new_i32(2);
            let c = Scm::new_cons(a, b);
            assert_eq!(c.car().to_i32(), 1i32);
        }
    }

    #[test]
    fn test_cdr() {
        unsafe {
            let a = Scm::new_i32(1);
            let b = Scm::new_i32(2);
            let c = Scm::new_cons(a, b);
            assert_eq!(c.cdr().to_i32(), 2i32);
        }
    }
}
