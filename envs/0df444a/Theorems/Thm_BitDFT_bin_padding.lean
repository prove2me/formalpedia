-- Prove2me | Theorems.Thm_BitDFT_bin_padding
-- name    : BitDFT.bin_padding
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-24T19:13:13.519085+00:00
-- url     : https://prove2.me/theorems/59095cd9-5625-4a11-b934-d4ebf422007d
-- title:
--   Pad a fixed-width binary word with leading zeroes
-- statement:
--   For natural numbers r,s,z, if z<2^r, then its binary word padded to width r+s is exactly s leading zero bits followed by its r-bit encoding. This gives the exact output layout needed to widen a clean multiplier result without changing its value.
-- source:
--   Binary output serialization for the exact integer-multiplication to finite-precision DFT transfer.

import Definitions.Def_IntMul_MultitapeModel
open IntMul

theorem BitDFT.bin_padding (r s z : ℕ) (hz : z < 2^r) :
    bin (r+s) z = List.replicate s false ++ bin r z := by sorry
