-- Prove2me | Theorems.Thm_Formalism_CountingSumsFrames_Har4_h_pow_mul_mem_gauss
-- name    : Formalism.CountingSumsFrames.Har4.h_pow_mul_mem_gauss
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T10:38:11.489804+00:00
-- url     : https://prove2.me/theorems/c99df248-0b40-4f49-9d54-14a5a36d3d68
-- title:
--   Har4: h pow mul mem gauss
-- statement:
--   The Har4 construction uses the h pow mul mem gauss property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PolynomialDimension/MultinomialDepth/SqrtFockGaussLatticeComparisonHolds.lean#L466-L472
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PolynomialDimension/MultinomialDepth/SqrtFockGaussLatticeComparisonHolds.lean#L466-L472

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

theorem Formalism.CountingSumsFrames.Har4.h_pow_mul_mem_gauss {K : Type} [Field K] {k : ℕ} (R : Subring K) (j : ℕ) (G : PolXY K k)
    (hG : G ∈ GaussLat R) : hXY K k ^ j * G ∈ GaussLat R := by sorry
