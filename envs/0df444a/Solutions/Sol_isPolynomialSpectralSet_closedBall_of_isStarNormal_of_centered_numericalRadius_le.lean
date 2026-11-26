-- Prove2me | solution 1 for isPolynomialSpectralSet_closedBall_of_isStarNormal_of_centered_numericalRadius_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T15:11:22.486513+00:00
-- url     : https://prove2.me/submissions/a99d0fdc-0587-4582-8db7-665555f32147

import Definitions.Def_Operator_Crouzeix_NormalPolynomialBound
import Definitions.Def_Operator_Crouzeix_SpectralSetMonotone
import Definitions.Def_Operator_NumericalRange_RadiusAffine
import Definitions.Def_Operator_Crouzeix_SpectralSetSuperset
import Theorems.Thm_isPolynomialSpectralSet_closedBall_centered_numericalRadius_of_isStarNormal
import Theorems.Thm_IsKPolynomialSpectralSet_mono_set
import Theorems.Thm_IsPolynomialSpectralSet_mono_set


set_option autoImplicit false
open Set
open scoped InnerProductSpace
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [CompleteSpace E]
theorem _root_.solution
    (A : E →L[ℂ] E) [IsStarNormal A] (c : ℂ) {R : ℝ}
    (hR : numericalRadius (A - c • 1) ≤ R) :
    IsPolynomialSpectralSet A (Metric.closedBall c R) :=
  (isPolynomialSpectralSet_closedBall_centered_numericalRadius_of_isStarNormal
    A c).mono_set (Metric.closedBall_subset_closedBall hR)
      (isCompact_closedBall c R)
