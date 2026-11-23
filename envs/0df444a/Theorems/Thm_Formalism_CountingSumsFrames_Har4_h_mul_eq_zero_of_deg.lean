-- Prove2me | Theorems.Thm_Formalism_CountingSumsFrames_Har4_h_mul_eq_zero_of_deg
-- name    : Formalism.CountingSumsFrames.Har4.h_mul_eq_zero_of_deg
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T10:38:01.116572+00:00
-- url     : https://prove2.me/theorems/36ed99b1-9bee-4ba5-9af8-762ba4855e2d
-- title:
--   Har4: h mul eq zero of deg
-- statement:
--   The Har4 construction uses the h mul eq zero of deg property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PolynomialDimension/MultinomialDepth/SqrtFockGaussLatticeComparisonHolds.lean#L793-L814
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PolynomialDimension/MultinomialDepth/SqrtFockGaussLatticeComparisonHolds.lean#L793-L814

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

theorem Formalism.CountingSumsFrames.Har4.h_mul_eq_zero_of_deg {K : Type} [Field K] {k A B : ℕ} (hAB : A = 0 ∨ B = 0) {w G : PolXY K k}
    (hw : w ∈ PolAB K k A B) (h : w = hXY K k * G) : w = 0 := by sorry
