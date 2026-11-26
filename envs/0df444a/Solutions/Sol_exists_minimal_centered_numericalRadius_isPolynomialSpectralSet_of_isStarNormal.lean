-- Prove2me | solution 1 for exists_minimal_centered_numericalRadius_isPolynomialSpectralSet_of_isStarNormal
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T15:43:53.369393+00:00
-- url     : https://prove2.me/submissions/ec4ee845-979f-4d92-86f4-a14c4cda7d14

import Definitions.Def_Operator_Crouzeix_NormalPolynomialBound
import Definitions.Def_Operator_Crouzeix_SpectralSetMonotone
import Definitions.Def_Operator_NumericalRange_RadiusAffine
import Definitions.Def_Operator_Crouzeix_SpectralSetSuperset
import Theorems.Thm_isPolynomialSpectralSet_closedBall_centered_numericalRadius_of_isStarNormal
import Theorems.Thm_exists_center_minimizing_numericalRadius


set_option autoImplicit false
open Set
open scoped InnerProductSpace
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [CompleteSpace E]
theorem _root_.solution
    [Nontrivial E] (A : E →L[ℂ] E) [IsStarNormal A] :
    ∃ c : ℂ,
      (∀ d : ℂ,
        numericalRadius (A - c • 1) ≤ numericalRadius (A - d • 1)) ∧
      IsPolynomialSpectralSet A
        (Metric.closedBall c (numericalRadius (A - c • 1))) := by
  obtain ⟨c, hc⟩ := exists_center_minimizing_numericalRadius A
  exact ⟨c, hc,
    isPolynomialSpectralSet_closedBall_centered_numericalRadius_of_isStarNormal A c⟩
