-- Prove2me | solution 1 for numericalRange_subset_closedBall
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T12:45:23.494137+00:00
-- url     : https://prove2.me/submissions/9c40b2c6-8dc3-4623-b267-8ac7599c6f04

import Mathlib.Analysis.Normed.Operator.Basic
import Definitions.Def_Operator_NumericalRange_Basic
import Definitions.Def_Operator_NumericalRange_Bounded
import Theorems.Thm_norm_le_of_mem_numericalRange

set_option autoImplicit false
open scoped InnerProductSpace
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
theorem _root_.solution (A : E →L[ℂ] E) :
    numericalRange A ⊆ Metric.closedBall 0 ‖A‖ := by
  intro z hz
  rw [Metric.mem_closedBall, dist_zero_right]
  exact norm_le_of_mem_numericalRange A hz
