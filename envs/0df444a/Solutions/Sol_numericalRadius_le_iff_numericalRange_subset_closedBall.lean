-- Prove2me | solution 1 for numericalRadius_le_iff_numericalRange_subset_closedBall
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T15:16:00.373405+00:00
-- url     : https://prove2.me/submissions/4583e578-a2f3-48cf-8e95-22e6f24f8aa6

import Definitions.Def_Operator_NumericalRange_Radius
import Definitions.Def_Operator_NumericalRange_RadiusCharacterization
import Theorems.Thm_numericalRadius_le_iff
import Theorems.Thm_mem_numericalRange
import Theorems.Thm_numericalRadiusSeminorm_apply
import Theorems.Thm_numericalRadius_neg
attribute [local simp] mem_numericalRange
attribute [local simp] numericalRadiusSeminorm_apply
attribute [local simp] numericalRadius_neg



set_option autoImplicit false
open Set
open scoped InnerProductSpace
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
theorem _root_.solution
    (A : E →L[ℂ] E) {r : ℝ} (hr : 0 ≤ r) :
    numericalRadius A ≤ r ↔
      numericalRange A ⊆ Metric.closedBall 0 r := by
  rw [numericalRadius_le_iff A hr]
  simp only [Set.subset_def, Metric.mem_closedBall, dist_zero_right]
