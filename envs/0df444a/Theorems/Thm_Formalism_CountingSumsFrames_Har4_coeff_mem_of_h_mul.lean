-- Prove2me | Theorems.Thm_Formalism_CountingSumsFrames_Har4_coeff_mem_of_h_mul
-- name    : Formalism.CountingSumsFrames.Har4.coeff_mem_of_h_mul
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T10:37:38.772157+00:00
-- url     : https://prove2.me/theorems/d8f48ddb-4957-4003-99bd-8cf61ec61ba8
-- title:
--   Har4: coeff mem of h mul
-- statement:
--   The Har4 construction uses the coeff mem of h mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PolynomialDimension/MultinomialDepth/SqrtFockGaussLatticeComparisonHolds.lean#L26-L65
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PolynomialDimension/MultinomialDepth/SqrtFockGaussLatticeComparisonHolds.lean#L26-L65

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

theorem Formalism.CountingSumsFrames.Har4.coeff_mem_of_h_mul {K : Type} [Field K] {k : ℕ} (R : Subring K) (i0 : Fin k) (G : PolXY K k)
    (hG : ∀ m, coeff m (hXY K k * G) ∈ R) : ∀ m, coeff m G ∈ R := by sorry
