-- Prove2me | solution 1 for isKPolynomialSpectralSet_closedBall_numericalRadius
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T15:08:51.134527+00:00
-- url     : https://prove2.me/submissions/5436ae0b-78e5-4356-8bcd-f734e0b9611f

import Definitions.Def_Operator_Crouzeix_NormalPolynomialBound
import Definitions.Def_Operator_Crouzeix_SpectralSetMonotone
import Definitions.Def_Operator_NumericalRange_RadiusAffine
import Definitions.Def_Operator_Crouzeix_SpectralSetSuperset
import Theorems.Thm_isKPolynomialSpectralSet_of_closure_numericalRange_subset
import Theorems.Thm_closure_numericalRange_subset_closedBall_numericalRadius


set_option autoImplicit false
open Set
open scoped InnerProductSpace
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [CompleteSpace E]
theorem _root_.solution
    (A : E →L[ℂ] E) :
    IsKPolynomialSpectralSet A (1 + Real.sqrt 2)
      (Metric.closedBall 0 (numericalRadius A)) :=
  isKPolynomialSpectralSet_of_closure_numericalRange_subset A
    (isCompact_closedBall (0 : ℂ) (numericalRadius A))
    (closure_numericalRange_subset_closedBall_numericalRadius A)
