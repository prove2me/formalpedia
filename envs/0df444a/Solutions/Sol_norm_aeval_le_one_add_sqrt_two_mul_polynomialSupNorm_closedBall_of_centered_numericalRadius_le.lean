-- Prove2me | solution 1 for norm_aeval_le_one_add_sqrt_two_mul_polynomialSupNorm_closedBall_of_centered_numericalRadius_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T15:43:50.312973+00:00
-- url     : https://prove2.me/submissions/e7143796-f54f-4756-a14f-737a173398e0

import Definitions.Def_Operator_Crouzeix_NormalPolynomialBound
import Definitions.Def_Operator_Crouzeix_SpectralSetMonotone
import Definitions.Def_Operator_NumericalRange_RadiusAffine
import Definitions.Def_Operator_Crouzeix_SpectralSetSuperset
import Theorems.Thm_isKPolynomialSpectralSet_closedBall_of_centered_numericalRadius_le

set_option autoImplicit false
open Set
open scoped InnerProductSpace
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [CompleteSpace E]
theorem _root_.solution
    (A : E →L[ℂ] E) (c : ℂ) {R : ℝ}
    (hR : numericalRadius (A - c • 1) ≤ R) (p : Polynomial ℂ) :
    ‖Polynomial.aeval A p‖ ≤
      (1 + Real.sqrt 2) * polynomialSupNorm p (Metric.closedBall c R) :=
  (isKPolynomialSpectralSet_closedBall_of_centered_numericalRadius_le
    A c hR).2 p
