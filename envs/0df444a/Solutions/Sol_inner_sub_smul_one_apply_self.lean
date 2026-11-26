-- Prove2me | solution 1 for inner_sub_smul_one_apply_self
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T12:54:01.588855+00:00
-- url     : https://prove2.me/submissions/e8b41fd7-15f6-428e-9f78-6e8028d7d72d

import Definitions.Def_Operator_NumericalRange_Basic
import Definitions.Def_Operator_NumericalRange_Helpers
import Theorems.Thm_mem_numericalRange
attribute [local simp] mem_numericalRange



set_option autoImplicit false
open scoped InnerProductSpace
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
theorem _root_.solution (A : E →L[ℂ] E) (l : ℂ)
    {x : E} (hx : ‖x‖ = 1) :
    ⟪x, (A - l • 1) x⟫_ℂ = ⟪x, A x⟫_ℂ - l := by
  simp only [sub_apply, smul_apply, one_apply_eq_self, inner_sub_right, inner_smul_right,
    inner_self_eq_norm_sq_to_K, hx]
  norm_num
