-- Prove2me | solution 1 for norm_le_one_add_sqrt_two_mul_of_auxiliary_re_inner_lower_bounds
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T12:50:39.652845+00:00
-- url     : https://prove2.me/submissions/25d5bfbf-7381-4359-a2bc-6e4b16b82b98

import Definitions.Def_Operator_Crouzeix_AuxOperator
import Definitions.Def_Operator_SpectralSet_Normal
import Definitions.Def_Operator_Crouzeix_Palencia
import Theorems.Thm_mem_numericalRange
import Theorems.Thm_norm_inv_norm_smul
attribute [local simp] mem_numericalRange


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
universe u
variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
variable [CompleteSpace E]
theorem _root_.solution
    (F G : E →L[ℂ] E) {m : ℝ}
    (hsymm : ‖F + star G‖ ≤ 2 * m)
    (hprod : ∀ x : E, ‖x‖ = 1 →
      -(m ^ 2) ≤ RCLike.re ⟪x, (F * G) x⟫_ℂ) :
    ‖F‖ ≤ (1 + Real.sqrt 2) * m := by
  have hm : 0 ≤ m := by
    nlinarith only [norm_nonneg (F + star G), hsymm]
  have hC : 0 ≤ (1 + Real.sqrt 2) * m :=
    mul_nonneg (add_nonneg zero_le_one (Real.sqrt_nonneg 2)) hm
  have hidentity : F * star F = F * star (F + star G) - F * G := by
    rw [star_add, star_star, mul_add, add_sub_cancel_right]
  have hunit : ∀ x : E, ‖x‖ = 1 →
      ‖(star F) x‖ ≤ (1 + Real.sqrt 2) * m := by
    intro x hx
    have hinnerSelf : ⟪(star F) x, (star F) x⟫_ℂ =
        ⟪x, (F * star F) x⟫_ℂ := by
      rw [mul_apply_eq_comp]
      exact ContinuousLinearMap.adjoint_inner_left F ((star F) x) x
    have hfirst : ‖⟪x, (F * star (F + star G)) x⟫_ℂ‖ ≤
        2 * m * ‖(star F) x‖ := by
      rw [mul_apply_eq_comp]
      rw [← ContinuousLinearMap.adjoint_inner_left F]
      calc
        ‖⟪(star F) x, star (F + star G) x⟫_ℂ‖ ≤
            ‖(star F) x‖ * ‖star (F + star G) x‖ := norm_inner_le_norm _ _
        _ ≤ ‖(star F) x‖ * ‖star (F + star G)‖ * ‖x‖ := by
          calc
            ‖(star F) x‖ * ‖star (F + star G) x‖ ≤
                ‖(star F) x‖ * (‖star (F + star G)‖ * ‖x‖) :=
              mul_le_mul_of_nonneg_left ((star (F + star G)).le_opNorm x)
                (norm_nonneg _)
            _ = ‖(star F) x‖ * ‖star (F + star G)‖ * ‖x‖ := by ring
        _ ≤ ‖(star F) x‖ * (2 * m) * 1 := by
          rw [norm_star, hx]
          gcongr
        _ = 2 * m * ‖(star F) x‖ := by ring
    have hquad : ‖(star F) x‖ ^ 2 ≤
        2 * m * ‖(star F) x‖ + m ^ 2 := by
      calc
        ‖(star F) x‖ ^ 2 = RCLike.re ⟪(star F) x, (star F) x⟫_ℂ := by
          rw [inner_self_eq_norm_sq]
        _ = RCLike.re ⟪x, (F * star F) x⟫_ℂ := congrArg RCLike.re hinnerSelf
        _ = RCLike.re ⟪x,
            (F * star (F + star G) - F * G) x⟫_ℂ := by rw [hidentity]
        _ = RCLike.re ⟪x, (F * star (F + star G)) x⟫_ℂ -
            RCLike.re ⟪x, (F * G) x⟫_ℂ := by
          rw [sub_apply, inner_sub_right, map_sub]
        _ ≤ ‖⟪x, (F * star (F + star G)) x⟫_ℂ‖ + m ^ 2 := by
          have hre := RCLike.re_le_norm ⟪x, (F * star (F + star G)) x⟫_ℂ
          nlinarith only [hre, hprod x hx]
        _ ≤ 2 * m * ‖(star F) x‖ + m ^ 2 := add_le_add hfirst le_rfl
    exact le_one_add_sqrt_two_mul_of_sq_le hm hquad
  rw [← norm_star F]
  apply ContinuousLinearMap.opNorm_le_bound' (star F) hC
  intro x hx
  have hxpos : 0 < ‖x‖ := (norm_pos_iff.mpr (norm_ne_zero_iff.mp hx))
  let y : E := ((‖x‖ : ℂ)⁻¹) • x
  have hy : ‖y‖ = 1 := norm_inv_norm_smul (norm_ne_zero_iff.mp hx)
  have hFy := hunit y hy
  have hnorm : ‖(star F) y‖ = ‖x‖⁻¹ * ‖(star F) x‖ := by
    simp only [y, map_smul, norm_smul, norm_inv, Complex.norm_real,
      Real.norm_eq_abs, abs_of_pos hxpos]
  rw [hnorm] at hFy
  calc
    ‖(star F) x‖ = ‖x‖ * (‖x‖⁻¹ * ‖(star F) x‖) := by
      field_simp
    _ ≤ ‖x‖ * ((1 + Real.sqrt 2) * m) :=
      mul_le_mul_of_nonneg_left hFy (norm_nonneg x)
    _ = (1 + Real.sqrt 2) * m * ‖x‖ := by ring
