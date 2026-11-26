-- Prove2me | solution 1 for isPolynomialSpectralSet_closedBall_numericalRadius_of_isStarNormal
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T15:08:56.973653+00:00
-- url     : https://prove2.me/submissions/01a97ad8-285b-4922-b301-0e81e08bb52a

import Definitions.Def_Operator_Crouzeix_NormalPolynomialBound
import Definitions.Def_Operator_Crouzeix_SpectralSetMonotone
import Definitions.Def_Operator_NumericalRange_RadiusAffine
import Definitions.Def_Operator_Crouzeix_SpectralSetSuperset
import Theorems.Thm_isPolynomialSpectralSet_of_isStarNormal_of_closure_numericalRange_subset
import Theorems.Thm_closure_numericalRange_subset_closedBall_numericalRadius


set_option autoImplicit false
open Set
open scoped InnerProductSpace
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [CompleteSpace E]
theorem _root_.solution
    (A : E →L[ℂ] E) [IsStarNormal A] :
    IsPolynomialSpectralSet A
      (Metric.closedBall 0 (numericalRadius A)) :=
  isPolynomialSpectralSet_of_isStarNormal_of_closure_numericalRange_subset A
    (isCompact_closedBall (0 : ℂ) (numericalRadius A))
    (closure_numericalRange_subset_closedBall_numericalRadius A)
