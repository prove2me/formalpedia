-- Prove2me | solution 1 for isKPolynomialSpectralSet_closedBall_centered_numericalRadius
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T14:59:32.431896+00:00
-- url     : https://prove2.me/submissions/f9056227-a9fe-4bb2-b215-f3e07f74178b

import Definitions.Def_Operator_Crouzeix_NormalPolynomialBound
import Definitions.Def_Operator_Crouzeix_SpectralSetMonotone
import Definitions.Def_Operator_NumericalRange_RadiusAffine
import Definitions.Def_Operator_Crouzeix_SpectralSetSuperset
import Theorems.Thm_isKPolynomialSpectralSet_of_closure_numericalRange_subset
import Theorems.Thm_closure_numericalRange_subset_closedBall_centered_numericalRadius


set_option autoImplicit false
open Set
open scoped InnerProductSpace
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [CompleteSpace E]
theorem _root_.solution
    (A : E →L[ℂ] E) (c : ℂ) :
    IsKPolynomialSpectralSet A (1 + Real.sqrt 2)
      (Metric.closedBall c (numericalRadius (A - c • 1))) :=
  isKPolynomialSpectralSet_of_closure_numericalRange_subset A
    (isCompact_closedBall c (numericalRadius (A - c • 1)))
    (closure_numericalRange_subset_closedBall_centered_numericalRadius A c)
