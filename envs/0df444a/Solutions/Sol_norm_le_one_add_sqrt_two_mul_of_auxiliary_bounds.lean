-- Prove2me | solution 1 for norm_le_one_add_sqrt_two_mul_of_auxiliary_bounds
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T12:48:34.40681+00:00
-- url     : https://prove2.me/submissions/c3433865-2852-4bae-b653-5b299033791d

import Definitions.Def_Operator_Crouzeix_AuxOperator
import Definitions.Def_Operator_SpectralSet_Normal
import Definitions.Def_Operator_Crouzeix_Palencia
section
open scoped InnerProductSpace
private theorem le_one_add_sqrt_two_mul_of_sq_le {x m : ℝ} (hm : 0 ≤ m)
    (hquad : x ^ 2 ≤ 2 * m * x + m ^ 2) : x ≤ (1 + Real.sqrt 2) * m := by
  have hsqrt_sq : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hsqrt_nonneg : 0 ≤ Real.sqrt 2 := Real.sqrt_nonneg 2
  have hsqrt_one : 1 ≤ Real.sqrt 2 := by
    nlinarith only [hsqrt_sq, hsqrt_nonneg]
  by_contra hbound
  have hlt : (1 + Real.sqrt 2) * m < x := lt_of_not_ge hbound
  have hroot_nonneg : 0 ≤ (1 + Real.sqrt 2) * m :=
    mul_nonneg (add_nonneg zero_le_one hsqrt_nonneg) hm
  have hx_pos : 0 < x := hroot_nonneg.trans_lt hlt
  have hfirst : 0 < x - (1 + Real.sqrt 2) * m := sub_pos.mpr hlt
  have hsecond : 0 < x + (Real.sqrt 2 - 1) * m :=
    add_pos_of_pos_of_nonneg hx_pos (mul_nonneg (sub_nonneg.mpr hsqrt_one) hm)
  have hprod_pos :
      0 < (x - (1 + Real.sqrt 2) * m) * (x + (Real.sqrt 2 - 1) * m) :=
    mul_pos hfirst hsecond
  have hfactor :
      (x - (1 + Real.sqrt 2) * m) * (x + (Real.sqrt 2 - 1) * m) =
        x ^ 2 - 2 * m * x - m ^ 2 := by
    nlinarith only [hsqrt_sq]
  rw [hfactor] at hprod_pos
  nlinarith only [hquad, hprod_pos]
universe u
variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
variable [CompleteSpace E]
end

set_option autoImplicit false
open scoped InnerProductSpace
theorem _root_.solution
    {B : Type*} [NonUnitalNormedRing B] [StarRing B] [CStarRing B]
    (F G : B) {m : ℝ}
    (hsymm : ‖F + star G‖ ≤ 2 * m) (hprod : ‖F * G‖ ≤ m ^ 2) :
    ‖F‖ ≤ (1 + Real.sqrt 2) * m := by
  have hm : 0 ≤ m := by
    nlinarith only [norm_nonneg (F + star G), hsymm]
  have hidentity : F * star F = F * star (F + star G) - F * G := by
    rw [star_add, star_star, mul_add, add_sub_cancel_right]
  have hbalance : ‖F‖ ^ 2 ≤ ‖F‖ * ‖F + star G‖ + ‖F * G‖ := by
    calc
      ‖F‖ ^ 2 = ‖F * star F‖ := by
        rw [CStarRing.norm_self_mul_star]
        ring
      _ = ‖F * star (F + star G) - F * G‖ := congrArg norm hidentity
      _ ≤ ‖F * star (F + star G)‖ + ‖F * G‖ := norm_sub_le _ _
      _ ≤ ‖F‖ * ‖star (F + star G)‖ + ‖F * G‖ :=
        add_le_add (norm_mul_le _ _) le_rfl
      _ = ‖F‖ * ‖F + star G‖ + ‖F * G‖ := by rw [norm_star]
  have hquad : ‖F‖ ^ 2 ≤ 2 * m * ‖F‖ + m ^ 2 := by
    calc
      ‖F‖ ^ 2 ≤ ‖F‖ * ‖F + star G‖ + ‖F * G‖ := hbalance
      _ ≤ ‖F‖ * (2 * m) + m ^ 2 :=
        add_le_add (mul_le_mul_of_nonneg_left hsymm (norm_nonneg F)) hprod
      _ = 2 * m * ‖F‖ + m ^ 2 := by ring
  exact le_one_add_sqrt_two_mul_of_sq_le hm hquad
