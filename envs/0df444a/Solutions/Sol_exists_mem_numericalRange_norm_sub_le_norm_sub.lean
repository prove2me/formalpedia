-- Prove2me | solution 1 for exists_mem_numericalRange_norm_sub_le_norm_sub
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T15:15:49.595033+00:00
-- url     : https://prove2.me/submissions/586b1995-efe1-408f-bcd9-dde8854f8dfd

import Definitions.Def_Operator_NumericalRange_Bounded
import Definitions.Def_Operator_NumericalRange_Stability
import Theorems.Thm_mem_numericalRange
attribute [local simp] mem_numericalRange



set_option autoImplicit false
open scoped InnerProductSpace
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
theorem _root_.solution
    (A B : E →L[ℂ] E) {z : ℂ} (hz : z ∈ numericalRange A) :
    ∃ w ∈ numericalRange B, ‖z - w‖ ≤ ‖A - B‖ := by
  obtain ⟨x, hx, rfl⟩ := (mem_numericalRange A z).mp hz
  refine ⟨⟪x, B x⟫_ℂ, (mem_numericalRange B _).2 ⟨x, hx, rfl⟩, ?_⟩
  calc
    ‖⟪x, A x⟫_ℂ - ⟪x, B x⟫_ℂ‖ = ‖⟪x, (A - B) x⟫_ℂ‖ := by
      simp only [sub_apply, inner_sub_right]
    _ ≤ ‖x‖ * ‖(A - B) x‖ := norm_inner_le_norm x _
    _ = ‖(A - B) x‖ := by rw [hx, one_mul]
    _ ≤ ‖A - B‖ * ‖x‖ := ContinuousLinearMap.le_opNorm _ _
    _ = ‖A - B‖ := by rw [hx, mul_one]
