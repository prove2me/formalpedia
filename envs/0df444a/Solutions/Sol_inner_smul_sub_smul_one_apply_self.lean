-- Prove2me | solution 1 for inner_smul_sub_smul_one_apply_self
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T12:47:49.193271+00:00
-- url     : https://prove2.me/submissions/b4083a67-9f61-49b4-8a0c-8929cf28286d

import Definitions.Def_Operator_NumericalRange_Basic
import Definitions.Def_Operator_NumericalRange_Helpers
import Theorems.Thm_mem_numericalRange
attribute [local simp] mem_numericalRange



set_option autoImplicit false
open scoped InnerProductSpace
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
theorem _root_.solution (c : ℂ) (z₀ : ℂ) (A : E →L[ℂ] E)
    {x : E} (hx : ‖x‖ = 1) :
    ⟪x, (c • (A - z₀ • 1)) x⟫_ℂ = c * (⟪x, A x⟫_ℂ - z₀) := by
  simp only [smul_apply, sub_apply, one_apply_eq_self, inner_smul_right, inner_sub_right,
    inner_self_eq_norm_sq_to_K, hx, mul_sub]
  norm_num
