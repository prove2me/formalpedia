-- Prove2me | solution 1 for isPolynomialSpectralSet_closedBall_of_isStarNormal_of_numericalRadius_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T15:43:39.519379+00:00
-- url     : https://prove2.me/submissions/f4314398-871d-4351-98d3-4112c6519fa8

import Definitions.Def_Operator_Crouzeix_NormalPolynomialBound
import Definitions.Def_Operator_Crouzeix_SpectralSetMonotone
import Definitions.Def_Operator_NumericalRange_RadiusAffine
import Definitions.Def_Operator_Crouzeix_SpectralSetSuperset
import Theorems.Thm_isPolynomialSpectralSet_closedBall_numericalRadius_of_isStarNormal
import Theorems.Thm_IsKPolynomialSpectralSet_mono_set
import Theorems.Thm_IsPolynomialSpectralSet_mono_set


set_option autoImplicit false
open Set
open scoped InnerProductSpace
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [CompleteSpace E]
theorem _root_.solution
    (A : E →L[ℂ] E) [IsStarNormal A] {R : ℝ}
    (hR : numericalRadius A ≤ R) :
    IsPolynomialSpectralSet A (Metric.closedBall 0 R) :=
  (isPolynomialSpectralSet_closedBall_numericalRadius_of_isStarNormal A).mono_set
    (Metric.closedBall_subset_closedBall hR) (isCompact_closedBall (0 : ℂ) R)
