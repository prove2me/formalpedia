-- Prove2me | Theorems.Thm_BitDFT_guard_precision_bound
-- name    : BitDFT.guard_precision_bound
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-24T12:01:46.167325+00:00
-- url     : https://prove2.me/theorems/fc05242a-78a6-475c-9b8f-fb27af391f65
-- title:
--   Guard precision suffices for the unnormalised error bound
-- statement:
--   For $n\ge1$ and every natural $b$, let $q=b+3\ell(n)+5$. Then $12n^3 2^b<2^q$. This is the numerical margin used when scaling a normalised output by $n$ and demanding absolute error below $2^{-b}$.
-- source:
--   Harvey and van der Hoeven, Integer multiplication is at least as hard as matrix transposition (2025), https://arxiv.org/abs/2503.22848, Sections 2–3.4; BitDFT transfer specification (24 October 2026) for explicit binary conventions and derived end-to-end formulations. Derived lemma — guard bits.

import Definitions.Def_BitDFT_Numerics
import Definitions.Def_IntMul_HvdH_KronMul
set_option autoImplicit false
noncomputable section
open scoped BigOperators
open BitDFT

theorem BitDFT.guard_precision_bound (n b : ℕ) (hn : 1 ≤ n) :
    12 * n ^ 3 * 2 ^ b < 2 ^ guardPrecision n b := by sorry
