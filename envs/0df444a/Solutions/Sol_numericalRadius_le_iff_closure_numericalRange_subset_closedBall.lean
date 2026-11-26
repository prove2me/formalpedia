-- Prove2me | solution 1 for numericalRadius_le_iff_closure_numericalRange_subset_closedBall
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T15:45:39.8208+00:00
-- url     : https://prove2.me/submissions/c5a6bc58-1b5f-452e-a372-82e107488b36

import Definitions.Def_Operator_NumericalRange_Radius
import Definitions.Def_Operator_NumericalRange_RadiusCharacterization
import Theorems.Thm_numericalRadius_le_iff_numericalRange_subset_closedBall

set_option autoImplicit false
open Set
open scoped InnerProductSpace
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
theorem _root_.solution
    (A : E →L[ℂ] E) {r : ℝ} (hr : 0 ≤ r) :
    numericalRadius A ≤ r ↔
      closure (numericalRange A) ⊆ Metric.closedBall 0 r := by
  constructor
  · intro h
    apply closure_minimal
    · exact (numericalRadius_le_iff_numericalRange_subset_closedBall A hr).1 h
    · exact Metric.isClosed_closedBall
  · intro h
    apply (numericalRadius_le_iff_numericalRange_subset_closedBall A hr).2
    exact subset_closure.trans h
