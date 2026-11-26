-- Prove2me | solution 1 for isPolynomialSpectralSet_closedBall_centered_numericalRadius_of_isStarNormal
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T15:00:23.084588+00:00
-- url     : https://prove2.me/submissions/5a885cec-a2e6-4b41-960e-14476c78aa7f

import Definitions.Def_Operator_Crouzeix_NormalPolynomialBound
import Definitions.Def_Operator_Crouzeix_SpectralSetMonotone
import Definitions.Def_Operator_NumericalRange_RadiusAffine
import Definitions.Def_Operator_Crouzeix_SpectralSetSuperset
import Theorems.Thm_isPolynomialSpectralSet_of_isStarNormal_of_closure_numericalRange_subset
import Theorems.Thm_closure_numericalRange_subset_closedBall_centered_numericalRadius


set_option autoImplicit false
open Set
open scoped InnerProductSpace
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [CompleteSpace E]
theorem _root_.solution
    (A : E →L[ℂ] E) [IsStarNormal A] (c : ℂ) :
    IsPolynomialSpectralSet A
      (Metric.closedBall c (numericalRadius (A - c • 1))) :=
  isPolynomialSpectralSet_of_isStarNormal_of_closure_numericalRange_subset A
    (isCompact_closedBall c (numericalRadius (A - c • 1)))
    (closure_numericalRange_subset_closedBall_centered_numericalRadius A c)
