-- Prove2me | Theorems.Thm_Formalism_CountingSumsFrames_Har4_coeff_cases
-- name    : Formalism.CountingSumsFrames.Har4.coeff_cases
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T23:29:55.283993+00:00
-- url     : https://prove2.me/theorems/1621135f-1c84-457f-a685-38b3b1a19fa8
-- title:
--   Har4: coeff cases
-- statement:
--   The Har4 construction uses the coeff cases property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PolynomialDimension/MultinomialDepth/SqrtFockGaussLatticeComparisonHolds.lean#L291-L296
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PolynomialDimension/MultinomialDepth/SqrtFockGaussLatticeComparisonHolds.lean#L291-L296

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
variable {K : Type} [Field K] [CharZero K] {k A B : ℕ} (R : Subring K)

theorem Formalism.CountingSumsFrames.Har4.coeff_cases {f : PolXY K k} (hf : f ∈ PolAB K k A B) (m : XY k →₀ ℕ) :
    coeff m f = 0 ∨ (xDeg m = A ∧ yDeg m = B) := by sorry
