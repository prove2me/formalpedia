-- Prove2me | solution 1 for hasDerivAt_crouzeixPolynomialScalarCompanion_of_not_mem_frontier
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T13:05:07.706845+00:00
-- url     : https://prove2.me/submissions/e1ab4f2e-3183-4ea1-9ad6-472693b213da

import Definitions.Def_Operator_Crouzeix_AuxOperator
import Mathlib.Analysis.Calculus.ParametricIntervalIntegral
import Definitions.Def_Operator_Crouzeix_ScalarCompanion
import Theorems.Thm_crouzeixPolynomialScalarCompanion_zero
import Theorems.Thm_crouzeixPolynomialScalarCompanionDeriv_zero
import Theorems.Thm_mem_numericalRange
attribute [local simp] mem_numericalRange


attribute [local simp] crouzeixPolynomialScalarCompanion_zero
attribute [local simp] crouzeixPolynomialScalarCompanionDeriv_zero

set_option autoImplicit false
open Complex Filter MeasureTheory Set spectrum
open scoped Interval Real
theorem _root_.solution
    (Omega : SmoothJordanDomain) (p : Polynomial ℂ) {z : ℂ}
    (hz : z ∉ frontier Omega.carrier) :
    HasDerivAt (crouzeixPolynomialScalarCompanion Omega p)
      (crouzeixPolynomialScalarCompanionDeriv Omega p z) z := by
  obtain ⟨δ, hδ, hball⟩ :=
    Metric.isOpen_iff.mp isClosed_frontier.isOpen_compl z hz
  let c : ℝ → ℂ := fun t ↦
    deriv Omega.boundaryParam t *
      star (Polynomial.eval (Omega.boundaryParam t) p)
  let F : ℂ → ℝ → ℂ := fun w t ↦
    c t * (Omega.boundaryParam t - w)⁻¹
  let F' : ℂ → ℝ → ℂ := fun w t ↦
    c t * (Omega.boundaryParam t - w)⁻¹ ^ 2
  have hsep : ∀ t, δ ≤ ‖Omega.boundaryParam t - z‖ := by
    intro t
    rw [← dist_eq_norm]
    apply le_of_not_gt
    intro hlt
    have hcompl := hball (by
      simpa only [Metric.mem_ball, dist_comm] using hlt)
    apply hcompl
    rw [← Omega.boundaryParam_range]
    exact mem_range_self t
  have hsep_local : ∀ t, ∀ w ∈ Metric.ball z (δ / 2),
      δ / 2 ≤ ‖Omega.boundaryParam t - w‖ := by
    intro t w hw
    have hwz : ‖w - z‖ < δ / 2 := by
      simpa only [Metric.mem_ball, dist_eq_norm] using hw
    have htri : ‖Omega.boundaryParam t - z‖ ≤
        ‖Omega.boundaryParam t - w‖ + ‖w - z‖ := by
      calc
        ‖Omega.boundaryParam t - z‖ =
            ‖(Omega.boundaryParam t - w) + (w - z)‖ := by ring_nf
        _ ≤ ‖Omega.boundaryParam t - w‖ + ‖w - z‖ := norm_add_le _ _
    linarith [hsep t]
  have hderiv : ∀ t, ∀ w ∈ Metric.ball z (δ / 2),
      HasDerivAt (fun x ↦ F x t) (F' w t) w := by
    intro t w hw
    have hne : Omega.boundaryParam t - w ≠ 0 := by
      intro heq
      have hzero : ‖Omega.boundaryParam t - w‖ = 0 := by rw [heq, norm_zero]
      linarith [hsep_local t w hw]
    have hsub : HasDerivAt (fun x : ℂ ↦ Omega.boundaryParam t - x) (-1) w := by
      have hfun : (fun x : ℂ ↦ Omega.boundaryParam t - x) =
          (fun _ : ℂ ↦ Omega.boundaryParam t) - id := by
        funext x
        rfl
      rw [hfun]
      simpa only [zero_sub] using
        (hasDerivAt_const w (Omega.boundaryParam t)).sub (hasDerivAt_id w)
    have hinv := hsub.inv hne
    have hmul := (hasDerivAt_const w (c t)).mul hinv
    have hfun : (fun x : ℂ ↦ c t * (Omega.boundaryParam t - x)⁻¹) =
        (fun _ : ℂ ↦ c t) * (fun x ↦ Omega.boundaryParam t - x)⁻¹ := by
      funext x
      rfl
    change HasDerivAt (fun x ↦ c t * (Omega.boundaryParam t - x)⁻¹)
      (c t * (Omega.boundaryParam t - w)⁻¹ ^ 2) w
    rw [hfun]
    simpa only [Pi.mul_apply, zero_mul, zero_add, neg_neg, one_div, inv_pow] using hmul
  have hccont : Continuous c := by
    apply Continuous.mul
    · exact Omega.boundaryParam_contDiff.continuous_deriv (by norm_num)
    · exact (p.continuous.comp
        Omega.boundaryParam_contDiff.continuous).star
  have hFcont : ∀ w ∈ Metric.ball z (δ / 2),
      ContinuousOn (F w) [[(0 : ℝ), 2 * Real.pi]] := by
    intro w hw
    have hden : ContinuousOn (fun t ↦ Omega.boundaryParam t - w)
        [[(0 : ℝ), 2 * Real.pi]] :=
      Omega.boundaryParam_contDiff.continuous.continuousOn.sub
        continuous_const.continuousOn
    have hne : ∀ t ∈ [[(0 : ℝ), 2 * Real.pi]],
        Omega.boundaryParam t - w ≠ 0 := by
      intro t ht heq
      have hzero : ‖Omega.boundaryParam t - w‖ = 0 := by rw [heq, norm_zero]
      linarith [hsep_local t w hw]
    have hfun : F w = c * (fun t ↦ Omega.boundaryParam t - w)⁻¹ := by
      funext t
      rfl
    rw [hfun]
    exact hccont.continuousOn.mul (hden.inv₀ hne)
  have hF'cont : ∀ w ∈ Metric.ball z (δ / 2),
      ContinuousOn (F' w) [[(0 : ℝ), 2 * Real.pi]] := by
    intro w hw
    have hden : ContinuousOn (fun t ↦ Omega.boundaryParam t - w)
        [[(0 : ℝ), 2 * Real.pi]] :=
      Omega.boundaryParam_contDiff.continuous.continuousOn.sub
        continuous_const.continuousOn
    have hne : ∀ t ∈ [[(0 : ℝ), 2 * Real.pi]],
        Omega.boundaryParam t - w ≠ 0 := by
      intro t ht heq
      have hzero : ‖Omega.boundaryParam t - w‖ = 0 := by rw [heq, norm_zero]
      linarith [hsep_local t w hw]
    have hfun : F' w = c * (fun t ↦ Omega.boundaryParam t - w)⁻¹ ^ 2 := by
      funext t
      rfl
    rw [hfun]
    exact hccont.continuousOn.mul ((hden.inv₀ hne).pow 2)
  let bound : ℝ → ℝ := fun t ↦ ‖c t‖ * (δ / 2)⁻¹ ^ 2
  have hboundInt : IntervalIntegrable bound volume (0 : ℝ) (2 * Real.pi) :=
    (hccont.norm.mul continuous_const).intervalIntegrable _ _
  have hFmeas : ∀ᶠ w in nhds z,
      AEStronglyMeasurable (F w)
        (volume.restrict (Ι (0 : ℝ) (2 * Real.pi))) := by
    filter_upwards [Metric.ball_mem_nhds z (half_pos hδ)] with w hw
    exact ((hFcont w hw).mono uIoc_subset_uIcc).aestronglyMeasurable
      measurableSet_uIoc
  have hFint : IntervalIntegrable (F z) volume (0 : ℝ) (2 * Real.pi) :=
    (hFcont z (Metric.mem_ball_self (half_pos hδ))).intervalIntegrable
  have hF'meas : AEStronglyMeasurable (F' z)
      (volume.restrict (Ι (0 : ℝ) (2 * Real.pi))) :=
    ((hF'cont z (Metric.mem_ball_self (half_pos hδ))).mono
      uIoc_subset_uIcc).aestronglyMeasurable measurableSet_uIoc
  have hbound : ∀ᵐ t ∂volume, t ∈ Ι (0 : ℝ) (2 * Real.pi) →
      ∀ w ∈ Metric.ball z (δ / 2), ‖F' w t‖ ≤ bound t := by
    filter_upwards with t
    intro ht w hw
    have hdenpos : 0 < ‖Omega.boundaryParam t - w‖ :=
      (half_pos hδ).trans_le (hsep_local t w hw)
    have hinv : ‖Omega.boundaryParam t - w‖⁻¹ ≤ (δ / 2)⁻¹ :=
      (inv_le_inv₀ hdenpos (half_pos hδ)).2 (hsep_local t w hw)
    dsimp only [F', bound]
    rw [norm_mul, norm_pow, norm_inv]
    gcongr
  have hdiff : ∀ᵐ t ∂volume, t ∈ Ι (0 : ℝ) (2 * Real.pi) →
      ∀ w ∈ Metric.ball z (δ / 2),
        HasDerivAt (fun x ↦ F x t) (F' w t) w := by
    filter_upwards with t
    intro ht w hw
    exact hderiv t w hw
  have hint := intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (Metric.ball_mem_nhds z (half_pos hδ)) hFmeas hFint hF'meas hbound hboundInt hdiff
  have hscaled :=
    (hasDerivAt_const z ((2 * (Real.pi : ℂ) * I)⁻¹)).mul hint.2
  have hcompanion : crouzeixPolynomialScalarCompanion Omega p = fun w ↦
      (2 * (Real.pi : ℂ) * I)⁻¹ *
        ∫ t in (0 : ℝ)..(2 * Real.pi), F w t := by
    funext w
    unfold crouzeixPolynomialScalarCompanion contourIntegral
    simp only [F, c, smul_eq_mul, mul_assoc]
  rw [hcompanion]
  have hpoint : (fun _ : ℂ ↦ (2 * (Real.pi : ℂ) * I)⁻¹) *
      (fun w ↦ ∫ t in (0 : ℝ)..(2 * Real.pi), F w t) =
      (fun w ↦ (2 * (Real.pi : ℂ) * I)⁻¹ *
        ∫ t in (0 : ℝ)..(2 * Real.pi), F w t) := by
    funext w
    rfl
  rw [← hpoint]
  simpa only [crouzeixPolynomialScalarCompanionDeriv, F', c, zero_mul,
    zero_add, mul_assoc] using hscaled
