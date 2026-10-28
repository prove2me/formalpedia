-- Prove2me | Theorems.Thm_BitDFT_boundary_signed_encoding
-- name    : BitDFT.boundary_signed_encoding
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-25T20:44:02.377445+00:00
-- url     : https://prove2.me/theorems/4367d788-fe8b-4bc8-9449-bf3694f16bd9
-- title:
--   Encode a signed boundary shift
-- statement:
--   Multiplying any signed integer z by 2^q preserves its sign and appends q zero bits to its fixed-width magnitude encoding. Thus the boundary output for the rescaling machine can be written by copying the signed encoding of the dimension and appending q zeros.
-- source:
--   Signed encoding consequence of the exact binary-shift lemma, used to specify the high-magnitude branch of output rescaling.

import Definitions.Def_BitDFT_Encoding
import Theorems.Thm_BitDFT_boundary_shift_encoding
import Mathlib.Tactic
set_option autoImplicit false
open BitDFT IntMul

theorem BitDFT.boundary_signed_encoding (w q : ℕ) (z : ℤ) : encInt (w+q) (z * (2^q : ℤ)) = [decide (z < 0)] ++ bin w z.natAbs ++ List.replicate q false := by sorry
