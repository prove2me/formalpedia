-- Prove2me | solution 1 for levy_foundations_public_largeSet_cosine_interval_lower_bound
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-10T12:22:41.236232+00:00
-- url     : https://prove2.me/submissions/689a197f-0d8a-4ed8-a908-3d330fd1a59e

import Mathlib.Probability.Independence.CharacteristicFunction
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal

/-- Integrating the Fourier cosine deficit bounds the reciprocal radius
when the spatial point is outside the radius-ε ball. -/
theorem solution (ε : ℝ) (hε : 0 < ε) (x : ℝ) (hx : ε ≤ |x|) :
    ε⁻¹ ≤ ∫ ξ in (0 : ℝ)..(2 / ε), (1 - Real.cos (ξ * x)) := by
    have hx_ne : x ≠ 0 := by
      intro h0; simp only [h0, abs_zero] at hx; linarith
    have hcos_int : IntervalIntegrable (fun ξ => Real.cos (ξ * x)) volume 0 (2/ε) :=
      (Real.continuous_cos.comp (continuous_id.mul continuous_const)).intervalIntegrable 0 (2/ε)
    have hmul : ∫ ξ in (0:ℝ)..(2/ε), Real.cos (ξ * x) = Real.sin (2 * x / ε) / x := by
      rw [intervalIntegral.integral_comp_mul_right (hc := hx_ne)]
      simp only [zero_mul, smul_eq_mul]
      rw [integral_cos, Real.sin_zero, sub_zero]
      rw [show (2 : ℝ) / ε * x = 2 * x / ε from by ring]
      rw [div_eq_mul_inv (Real.sin _) x, mul_comm]
    have hcomp : ∫ ξ in (0:ℝ)..(2/ε), (1 - Real.cos (ξ * x)) =
        2/ε - Real.sin (2 * x / ε) / x := by
      rw [intervalIntegral.integral_sub intervalIntegrable_const hcos_int,
        intervalIntegral.integral_const, smul_eq_mul, mul_one, hmul]
      ring
    rw [hcomp]
    have hsin_bd : Real.sin (2 * x / ε) / x ≤ 1/ε := by
      have habs : |Real.sin (2 * x / ε) / x| ≤ 1/ε := by
        rw [abs_div, div_le_div_iff₀ (abs_pos.mpr hx_ne) hε]
        nlinarith [Real.abs_sin_le_one (2 * x / ε)]
      linarith [le_abs_self (Real.sin (2 * x / ε) / x)]
    have h1e : (1:ℝ)/ε = ε⁻¹ := one_div ε
    have h2e : (2:ℝ)/ε = 2 * ε⁻¹ := by rw [div_eq_mul_inv]
    linarith

