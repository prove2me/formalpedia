-- Prove2me | Theorems.Thm_BitDFT_vector_encoding_length
-- name    : BitDFT.vector_encoding_length
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-24T12:01:41.830545+00:00
-- url     : https://prove2.me/theorems/c4c1bdcd-4820-48c9-9efa-6b35abc085a1
-- title:
--   Exact binary length of a complex vector
-- statement:
--   Encoding $n$ Gaussian integer pairs with $w$ magnitude bits per real or imaginary part produces exactly $2n(w+1)$ bits, including two sign bits per coordinate. This length statement needs no coefficient bound.
-- source:
--   Harvey and van der Hoeven, Integer multiplication is at least as hard as matrix transposition (2025), https://arxiv.org/abs/2503.22848, Sections 2–3.4; BitDFT transfer specification (24 October 2026) for explicit binary conventions and derived end-to-end formulations. Encoding foundation.

import Definitions.Def_BitDFT_Numerics
import Definitions.Def_IntMul_HvdH_KronMul
set_option autoImplicit false
noncomputable section
open scoped BigOperators
open BitDFT

theorem BitDFT.vector_encoding_length {n : ℕ} (w : ℕ) (U : Fin n → ℤ × ℤ) :
    (encVector w U).length = 2 * n * (w + 1) := by sorry
