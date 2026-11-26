-- Prove2me | solution 1 for norm_intervalIntegral_smul_le_of_ae_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T13:35:33.121608+00:00
-- url     : https://prove2.me/submissions/29ddfade-7dc0-4b7a-a3b8-fef587681031

import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.Positive
import Mathlib.Analysis.InnerProductSpace.StarOrder
import Mathlib.Analysis.CStarAlgebra.ContinuousLinearMap
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Basic
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Definitions.Def_Operator_Crouzeix_PositiveKernelBound
import Theorems.Thm_norm_inner_apply_le_sqrt_mul_sqrt_of_nonneg
import Theorems.Thm_opNorm_le_of_forall_norm_inner_le
import Theorems.Thm_sqrt_mul_sqrt_le_of_pos
import Theorems.Thm_norm_inner_le_of_forall_pos_le

set_option autoImplicit false
open ContinuousLinearMap MeasureTheory
open scoped InnerProductSpace
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
theorem _root_.solution {K : ℝ → E →L[ℂ] E} {f : ℝ → ℂ}
    {a b c M : ℝ} (hab : a ≤ b) (hK : IntervalIntegrable K volume a b)
    (hfK : IntervalIntegrable (fun t => f t • K t) volume a b)
    (hpos : ∀ᵐ t ∂(volume.restrict (Set.Ioc a b)), 0 ≤ K t)
    (hnorm : ∫ t in a..b, K t = c • (1 : E →L[ℂ] E))
    (hc : 0 ≤ c) (hM : 0 ≤ M) (hf : ∀ᵐ t ∂(volume.restrict (Set.Ioc a b)), ‖f t‖ ≤ M) :
    ‖∫ t in a..b, f t • K t‖ ≤ c * M := by
  rw [intervalIntegral.integral_of_le hab] at hnorm ⊢
  have hK' : IntegrableOn K (Set.Ioc a b) :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le hab).mp hK
  have hfK' : IntegrableOn (fun t => f t • K t) (Set.Ioc a b) :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le hab).mp hfK
  -- the quadratic forms `t ↦ re ⟪x, K t x⟫` are integrable with integral `c * ‖x‖ ^ 2`
  have hKx : ∀ x : E, Integrable (fun t => K t x) (volume.restrict (Set.Ioc a b)) := fun x =>
    (ContinuousLinearMap.apply ℂ E x).integrable_comp hK'
  have hgint : ∀ x : E,
      Integrable (fun t => RCLike.re ⟪x, K t x⟫_ℂ) (volume.restrict (Set.Ioc a b)) := fun x =>
    ((hKx x).const_inner x).re
  have hgval : ∀ x : E, ∫ t in Set.Ioc a b, RCLike.re ⟪x, K t x⟫_ℂ = c * ‖x‖ ^ 2 := by
    intro x
    rw [integral_re ((hKx x).const_inner x), integral_inner (hKx x),
      ← ContinuousLinearMap.integral_apply hK', hnorm, smul_apply, one_apply_eq_self,
      RCLike.real_smul_eq_coe_smul (K := ℂ), inner_smul_right, RCLike.re_ofReal_mul,
      inner_self_eq_norm_sq]
  refine opNorm_le_of_forall_norm_inner_le (mul_nonneg hc hM) fun x y => ?_
  refine norm_inner_le_of_forall_pos_le x y fun s hs => ?_
  have hΦy : Integrable (fun t => (f t • K t) y) (volume.restrict (Set.Ioc a b)) :=
    (ContinuousLinearMap.apply ℂ E y).integrable_comp hfK'
  rw [ContinuousLinearMap.integral_apply hfK', ← integral_inner hΦy]
  refine (norm_integral_le_integral_norm _).trans ?_
  have hpt : ∀ᵐ t ∂(volume.restrict (Set.Ioc a b)),
      ‖⟪x, (f t • K t) y⟫_ℂ‖ ≤
        M * ((s * RCLike.re ⟪x, K t x⟫_ℂ + RCLike.re ⟪y, K t y⟫_ℂ / s) / 2) := by
    filter_upwards [hpos, hf] with t hKt hft
    have hKt' : IsPositive (K t) := (nonneg_iff_isPositive _).mp hKt
    rw [smul_apply, inner_smul_right, norm_mul]
    calc ‖f t‖ * ‖⟪x, K t y⟫_ℂ‖
        ≤ M * (Real.sqrt (RCLike.re ⟪x, K t x⟫_ℂ) * Real.sqrt (RCLike.re ⟪y, K t y⟫_ℂ)) :=
          mul_le_mul hft (norm_inner_apply_le_sqrt_mul_sqrt_of_nonneg hKt x y)
            (norm_nonneg _) hM
      _ ≤ M * ((s * RCLike.re ⟪x, K t x⟫_ℂ + RCLike.re ⟪y, K t y⟫_ℂ / s) / 2) :=
          mul_le_mul_of_nonneg_left
            (sqrt_mul_sqrt_le_of_pos (hKt'.re_inner_nonneg_right x)
              (hKt'.re_inner_nonneg_right y) hs) hM
  have hrhs : Integrable
      (fun t => M * ((s * RCLike.re ⟪x, K t x⟫_ℂ + RCLike.re ⟪y, K t y⟫_ℂ / s) / 2))
      (volume.restrict (Set.Ioc a b)) :=
    ((((hgint x).const_mul s).add ((hgint y).div_const s)).div_const 2).const_mul M
  calc ∫ t in Set.Ioc a b, ‖⟪x, (f t • K t) y⟫_ℂ‖
      ≤ ∫ t in Set.Ioc a b,
          M * ((s * RCLike.re ⟪x, K t x⟫_ℂ + RCLike.re ⟪y, K t y⟫_ℂ / s) / 2) :=
        integral_mono_ae (hΦy.const_inner x).norm hrhs hpt
    _ = M * ((s * (c * ‖x‖ ^ 2) + c * ‖y‖ ^ 2 / s) / 2) := by
        rw [integral_const_mul, integral_div,
          integral_add ((hgint x).const_mul s) ((hgint y).div_const s),
          integral_const_mul, integral_div, hgval x, hgval y]
