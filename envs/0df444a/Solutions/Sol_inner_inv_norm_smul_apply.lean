-- Prove2me | solution 1 for inner_inv_norm_smul_apply
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T13:02:39.043846+00:00
-- url     : https://prove2.me/submissions/31f6e1c2-231b-4dae-a6b6-106076c252cd

import Definitions.Def_Operator_NumericalRange_Basic
import Definitions.Def_Operator_NumericalRange_Helpers

set_option autoImplicit false
open scoped InnerProductSpace
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
theorem _root_.solution (A : E →L[ℂ] E) {x : E} (hx : x ≠ 0) :
    ⟪((‖x‖ : ℂ)⁻¹) • x, A (((‖x‖ : ℂ)⁻¹) • x)⟫_ℂ =
    ⟪x, A x⟫_ℂ / (‖x‖ : ℂ) ^ 2 := by
  rw [map_smul, inner_smul_left, inner_smul_right, ← mul_assoc,
    Complex.conj_mul']
  rw [norm_inv, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (norm_nonneg x)]
  push_cast
  field_simp [norm_ne_zero_iff.mpr hx]
