-- Prove2me | Theorems.Thm_BitDFT_boundary_shift_encoding
-- name    : BitDFT.boundary_shift_encoding
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-25T20:39:31.646+00:00
-- url     : https://prove2.me/theorems/d5edfddc-4523-4a32-ac66-770f43df1fbb
-- title:
--   Encode the boundary magnitude as a binary shift
-- statement:
--   For any natural number n and widths w and q, the fixed-width binary encoding of n multiplied by 2^q is the width-w encoding of n followed by q zero bits. In particular, when n fits in width w, the exact boundary product used by output rescaling has a direct shift encoding.
-- source:
--   Exact encoding lemma for the boundary branch of the finite-precision Fourier output-rescaling machine. It handles the magnitude 2^q that cannot be passed to a q-bit multiplication call.

import Definitions.Def_IntMul_MultitapeModel
import Mathlib.Data.List.OfFn
import Mathlib.Data.Nat.Bitwise
set_option autoImplicit false
open IntMul

theorem BitDFT.boundary_shift_encoding (w n q : ℕ) : bin (w+q) (n*2^q) = bin w n ++ List.replicate q false := by sorry
