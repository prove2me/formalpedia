-- Prove2me | solution 1 for e7_weighted_integral_functional_lipschitz
-- status  : ACCEPTED   (prove)
-- author  : @ducloc
-- created : 2026-11-08T07:59:49.555707+00:00
-- url     : https://prove2.me/submissions/09e37511-fa3e-4d23-94a5-2e804399bc64

import Mathlib

open MeasureTheory Set Filter

theorem solution {V : Type*} [NormedAddCommGroup V]
    (μ : Measure ℝ) (w : ℝ → ℝ) (q : V → ℝ → ℝ)
    (C M : ℝ)
    (hw_nonneg : ∀ᵐ t ∂μ, 0 ≤ w t)
    (hw_int : Integrable w μ)
    (hw_value : (∫ t, w t ∂μ) = M)
    (hpath_lip : ∀ x y t, ‖q x t - q y t‖ ≤ C * ‖x - y‖)
    (hweighted_int : ∀ x, Integrable (fun t => w t * q x t) μ) :
    ∀ x y, ‖(∫ t, w t * q x t ∂μ) -
      ∫ t, w t * q y t ∂μ‖ ≤ C * M * ‖x - y‖ := by
  intro x y
  have hM : 0 ≤ M := by
    rw [← hw_value]
    exact integral_nonneg_of_ae hw_nonneg
  have hsub : Integrable (fun t => w t * q x t - w t * q y t) μ :=
    (hweighted_int x).sub (hweighted_int y)
  have hdiff : (∫ t, w t * q x t ∂μ) - ∫ t, w t * q y t ∂μ =
      ∫ t, w t * (q x t - q y t) ∂μ := by
    rw [← integral_sub (hweighted_int x) (hweighted_int y)]
    apply integral_congr_ae
    filter_upwards with t
    ring
  rw [hdiff]
  have hnorm_int : Integrable (fun t => w t * ‖q x t - q y t‖) μ := by
    refine hsub.norm.congr ?_
    filter_upwards [hw_nonneg] with t ht
    rw [show w t * q x t - w t * q y t = w t * (q x t - q y t) by ring]
    rw [norm_mul, Real.norm_of_nonneg ht]
  calc ‖∫ t, w t * (q x t - q y t) ∂μ‖
      ≤ ∫ t, ‖w t * (q x t - q y t)‖ ∂μ := norm_integral_le_integral_norm _
    _ = ∫ t, w t * ‖q x t - q y t‖ ∂μ := by
        apply integral_congr_ae
        filter_upwards [hw_nonneg] with t ht
        rw [norm_mul, Real.norm_of_nonneg ht]
    _ ≤ ∫ t, w t * (C * ‖x - y‖) ∂μ := by
        apply integral_mono_ae hnorm_int (hw_int.mul_const _)
        filter_upwards [hw_nonneg] with t ht
        exact mul_le_mul_of_nonneg_left (hpath_lip x y t) ht
    _ = C * M * ‖x - y‖ := by
        rw [integral_mul_const (C * ‖x - y‖) w, hw_value]
        ring
