-- Prove2me | Theorems.Thm_CorrelatedAuctionComplexity_Main_hdfpa_membership_tfnp
-- name    : CorrelatedAuctionComplexity.Main.hdfpa_membership_tfnp
-- status  : Open
-- author  : @Mr Robbins
-- created : 2026-11-23T08:28:33.397542+00:00
-- url     : https://prove2.me/theorems/f972d32d-3951-4475-af67-321ac31087b7
-- title:
--   Lemma 16 — TFNP membership of variable-accuracy HDFPA search
-- statement:
--   Assuming the polynomial-time exact expected-utility evaluator of Lemma 15, the variable-accuracy HDFPA equilibrium problem is polynomially balanced, polynomially verifiable on its decidable valid-instance domain, and total. Rational approximate equilibria exist by existence of Nash equilibria followed by grid rounding, with the canonical profile encoding bounded by `witnessBound`.
-- source:
--   Chen–Chen–Cui–Pires–Stockwell, STOC 2027 submission #324, Lemma 16 and proof, pp. 20–21; utility computation is Lemma 15, pp. 19–20.

import Definitions.Def_CorrelatedAuctionComplexity_Main_NashFixedSearch

set_option autoImplicit false

theorem CorrelatedAuctionComplexity.Main.hdfpa_membership_tfnp :
    ExpectedUtilityPolytime → IsTFNP hVariableAccuracy := by sorry
