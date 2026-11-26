-- Prove2me | solution 1 for isKPolynomialSpectralSet_closedBall_of_centered_numericalRadius_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T15:10:01.974346+00:00
-- url     : https://prove2.me/submissions/efa563fa-5436-4a85-afd8-9818ba06a04d

import Definitions.Def_Operator_Crouzeix_NormalPolynomialBound
import Definitions.Def_Operator_Crouzeix_SpectralSetMonotone
import Definitions.Def_Operator_NumericalRange_RadiusAffine
import Definitions.Def_Operator_Crouzeix_SpectralSetSuperset
import Theorems.Thm_isKPolynomialSpectralSet_closedBall_centered_numericalRadius
import Theorems.Thm_IsKPolynomialSpectralSet_mono_set
import Theorems.Thm_IsPolynomialSpectralSet_mono_set


set_option autoImplicit false
open Set
open scoped InnerProductSpace
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [CompleteSpace E]
theorem _root_.solution
    (A : E →L[ℂ] E) (c : ℂ) {R : ℝ}
    (hR : numericalRadius (A - c • 1) ≤ R) :
    IsKPolynomialSpectralSet A (1 + Real.sqrt 2) (Metric.closedBall c R) :=
  (isKPolynomialSpectralSet_closedBall_centered_numericalRadius A c).mono_set
    (by positivity) (Metric.closedBall_subset_closedBall hR)
    (isCompact_closedBall c R)
