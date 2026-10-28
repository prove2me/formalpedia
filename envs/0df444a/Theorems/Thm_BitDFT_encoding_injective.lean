-- Prove2me | Theorems.Thm_BitDFT_encoding_injective
-- name    : BitDFT.encoding_injective
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-24T12:01:32.839242+00:00
-- url     : https://prove2.me/theorems/10e28867-a7fe-42f3-b872-fe6af7e5ec67
-- title:
--   Sign-magnitude encoding is injective within its width
-- statement:
--   If two integers have magnitude strictly less than $2^w$, equality of their width-$w$ sign-magnitude encodings implies equality of the integers. Includes $w=0$, where the range condition permits only zero.
-- source:
--   Harvey and van der Hoeven, Integer multiplication is at least as hard as matrix transposition (2025), https://arxiv.org/abs/2503.22848, Sections 2–3.4; BitDFT transfer specification (24 October 2026) for explicit binary conventions and derived end-to-end formulations. Encoding foundation.

import Definitions.Def_BitDFT_Numerics
import Definitions.Def_IntMul_HvdH_KronMul
set_option autoImplicit false
noncomputable section
open scoped BigOperators
open BitDFT

theorem BitDFT.encoding_injective (w : ℕ) (a b : ℤ)
    (ha : a.natAbs < 2 ^ w) (hb : b.natAbs < 2 ^ w)
    (h : encInt w a = encInt w b) : a = b := by sorry
