-- Prove2me | solution 1 for re_inner_mul_lower_iff_norm_adjoint_sub_sq_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T13:36:15.276894+00:00
-- url     : https://prove2.me/submissions/a548c982-1d1d-454d-a75b-b6ce9a0b21fc

import Definitions.Def_Operator_Crouzeix_AuxOperator
import Definitions.Def_Operator_SpectralSet_Normal
import Definitions.Def_Operator_Crouzeix_Palencia
import Theorems.Thm_four_mul_re_inner_mul_eq_norm_adjoint_add_sq_sub

set_option autoImplicit false
open scoped InnerProductSpace
universe u
variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
variable [CompleteSpace E]
theorem _root_.solution
    (F G : E →L[ℂ] E) (x : E) (m : ℝ) :
    -(m ^ 2) ≤ RCLike.re ⟪x, (F * G) x⟫_ℂ ↔
      ‖(star F - G) x‖ ^ 2 ≤ ‖(star F + G) x‖ ^ 2 + 4 * m ^ 2 := by
  have hidentity := four_mul_re_inner_mul_eq_norm_adjoint_add_sq_sub F G x
  constructor <;> intro hbound <;> nlinarith only [hidentity, hbound]
