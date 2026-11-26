-- Prove2me | solution 1 for exists_norm_eq_one_norm_inner_apply_eq_numericalRadius
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T15:45:43.749249+00:00
-- url     : https://prove2.me/submissions/418f2407-8710-42bc-a716-734f1fe08be9

import Definitions.Def_Operator_NumericalRange_Compact
import Definitions.Def_Operator_NumericalRange_Radius
import Definitions.Def_Operator_NumericalRange_RadiusFiniteDimensional
import Theorems.Thm_exists_mem_numericalRange_norm_eq_numericalRadius
import Theorems.Thm_mem_numericalRange
attribute [local simp] mem_numericalRange



set_option autoImplicit false
open scoped InnerProductSpace
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [FiniteDimensional ℂ E] [Nontrivial E]
theorem _root_.solution
    (A : E →L[ℂ] E) :
    ∃ x : E, ‖x‖ = 1 ∧ ‖⟪x, A x⟫_ℂ‖ = numericalRadius A := by
  obtain ⟨z, hz, hnorm⟩ :=
    exists_mem_numericalRange_norm_eq_numericalRadius A
  obtain ⟨x, hx, rfl⟩ := (mem_numericalRange A z).mp hz
  exact ⟨x, hx, hnorm⟩
