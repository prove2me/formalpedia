-- Prove2me | Theorems.Thm_BitDFT_encComplex_length
-- name    : BitDFT.encComplex_length
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-25T00:53:02.379933+00:00
-- url     : https://prove2.me/theorems/e8bc5459-455d-42cf-8e8f-9707a2a1cd63
-- title:
--   A complex coordinate has a fixed signed-field length
-- statement:
--   For any fixed magnitude width $w$, each real or imaginary signed integer field uses one sign bit and $w$ magnitude bits. Thus one complex coordinate occupies exactly two fields:
--
--   $$|\operatorname{encComplex}_w(z)|=2(w+1).$$
--
--   Together with the first-coordinate decomposition, this gives a uniform stride for advancing through encoded vector records.
-- source:
--   A fixed-record stride lemma used by the coordinate scanner in the output-scaling pass.

import Definitions.Def_BitDFT_Encoding
import Mathlib.Data.List.OfFn
set_option autoImplicit false
open BitDFT IntMul

theorem BitDFT.encComplex_length (w : ℕ) (z : ℤ × ℤ) :
    (encComplex w z).length = 2 * (w + 1) := by sorry
