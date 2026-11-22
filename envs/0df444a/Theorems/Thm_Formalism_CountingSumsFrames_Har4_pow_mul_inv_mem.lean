-- Prove2me | Theorems.Thm_Formalism_CountingSumsFrames_Har4_pow_mul_inv_mem
-- name    : Formalism.CountingSumsFrames.Har4.pow_mul_inv_mem
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T23:31:44.085192+00:00
-- url     : https://prove2.me/theorems/3881a97c-0941-48e9-b841-5bbf0dfcc7f3
-- title:
--   Har4: pow mul inv mem
-- statement:
--   The Har4 construction uses the pow mul inv mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PolynomialDimension/MultinomialDepth/SqrtFockGaussLatticeComparisonHolds.lean#L218-L229
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PolynomialDimension/MultinomialDepth/SqrtFockGaussLatticeComparisonHolds.lean#L218-L229

import Definitions.Def_Formalism_PolynomialDimension_StatementHar
import Definitions.Def_Formalism_PolynomialDimension_MultinomialDepth_HarmonicDecompositionHolds
import Definitions.Def_Formalism_PolynomialDimension_MultinomialDepth_DiagLaplacianDivPowMemSqrtFockLattice
import Definitions.Def_Formalism_PolynomialDimension_MultinomialDepth_SqrtFockGaussLatticeComparisonHolds
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Finset MvPolynomial
open Formalism Formalism.CountingSumsFrames
open Formalism.CountingSumsFrames.Har4

theorem Formalism.CountingSumsFrames.Har4.pow_mul_inv_mem {K : Type} [Field K] [CharZero K] (R : Subring K) {p : ℕ} (hp : p.Prime)
    (hR : PLocal R p) {M e : ℕ} (hM : M ≠ 0) (hv : M.factorization p ≤ e) :
    (p : K) ^ e * (M : K)⁻¹ ∈ R := by sorry
