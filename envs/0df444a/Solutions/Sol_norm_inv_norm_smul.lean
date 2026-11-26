-- Prove2me | solution 1 for norm_inv_norm_smul
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T12:34:18.782791+00:00
-- url     : https://prove2.me/submissions/723c5722-d26b-44e0-b777-526677d9b7b3

import Definitions.Def_Operator_NumericalRange_Basic
import Definitions.Def_Operator_NumericalRange_Helpers

set_option autoImplicit false
open scoped InnerProductSpace
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
theorem _root_.solution {x : E} (hx : x ≠ 0) :
    ‖((‖x‖ : ℂ)⁻¹) • x‖ = 1 := by
  rw [norm_smul, norm_inv, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (norm_nonneg x), inv_mul_cancel₀ (norm_ne_zero_iff.mpr hx)]
