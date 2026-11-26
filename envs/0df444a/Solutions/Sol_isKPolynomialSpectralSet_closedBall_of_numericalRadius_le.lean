-- Prove2me | solution 1 for isKPolynomialSpectralSet_closedBall_of_numericalRadius_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T15:43:12.385078+00:00
-- url     : https://prove2.me/submissions/ac13b9a9-2d3f-41ac-9a7c-8d9802f56d4e

import Definitions.Def_Operator_Crouzeix_NormalPolynomialBound
import Definitions.Def_Operator_Crouzeix_SpectralSetMonotone
import Definitions.Def_Operator_NumericalRange_RadiusAffine
import Definitions.Def_Operator_Crouzeix_SpectralSetSuperset
import Theorems.Thm_isKPolynomialSpectralSet_closedBall_numericalRadius
import Theorems.Thm_IsKPolynomialSpectralSet_mono_set
import Theorems.Thm_IsPolynomialSpectralSet_mono_set


set_option autoImplicit false
open Set
open scoped InnerProductSpace
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [CompleteSpace E]
theorem _root_.solution
    (A : E →L[ℂ] E) {R : ℝ} (hR : numericalRadius A ≤ R) :
    IsKPolynomialSpectralSet A (1 + Real.sqrt 2)
      (Metric.closedBall 0 R) :=
  (isKPolynomialSpectralSet_closedBall_numericalRadius A).mono_set
    (by positivity) (Metric.closedBall_subset_closedBall hR)
    (isCompact_closedBall (0 : ℂ) R)
