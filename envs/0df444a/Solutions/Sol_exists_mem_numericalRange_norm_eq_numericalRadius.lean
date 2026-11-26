-- Prove2me | solution 1 for exists_mem_numericalRange_norm_eq_numericalRadius
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T15:15:27.272888+00:00
-- url     : https://prove2.me/submissions/8c2f39ac-05a5-4de9-871e-105761373a16

import Definitions.Def_Operator_NumericalRange_Compact
import Definitions.Def_Operator_NumericalRange_Radius
import Definitions.Def_Operator_NumericalRange_RadiusFiniteDimensional
import Theorems.Thm_isCompact_numericalRange
import Theorems.Thm_norm_le_numericalRadius
import Theorems.Thm_numericalRange_eq_image


set_option autoImplicit false
open scoped InnerProductSpace
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [FiniteDimensional ℂ E] [Nontrivial E]
theorem _root_.solution
    (A : E →L[ℂ] E) :
    ∃ z ∈ numericalRange A, ‖z‖ = numericalRadius A := by
  obtain ⟨x, hx⟩ : (Metric.sphere (0 : E) 1).Nonempty :=
    NormedSpace.sphere_nonempty.mpr zero_le_one
  have hW : (numericalRange A).Nonempty := by
    refine ⟨⟪x, A x⟫_ℂ, ?_⟩
    rw [numericalRange_eq_image]
    exact ⟨x, hx, rfl⟩
  obtain ⟨z, hz, hmax⟩ :=
    (isCompact_numericalRange A).exists_isMaxOn hW continuous_norm.continuousOn
  refine ⟨z, hz, le_antisymm (norm_le_numericalRadius A hz) ?_⟩
  unfold numericalRadius
  exact Real.iSup_le (fun w => Real.iSup_le (fun hw => hmax hw) (norm_nonneg z))
    (norm_nonneg z)
