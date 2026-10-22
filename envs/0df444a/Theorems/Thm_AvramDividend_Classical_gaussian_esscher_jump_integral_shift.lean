-- Prove2me | Theorems.Thm_AvramDividend_Classical_gaussian_esscher_jump_integral_shift
-- name    : AvramDividend.Classical.gaussian_esscher_jump_integral_shift
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-21T08:19:29.15712+00:00
-- url     : https://prove2.me/theorems/445f813f-0a57-4ae4-8590-00056d5f0b61
-- title:
--   Real-valued Lévy jump integral under Esscher shift
-- statement:
--   For any measure on real jump magnitudes and any real truncation function, assuming integrability of the original and shifted Lévy jump compensators, the quadratic Esscher compensator and the drift correction, integrate the exact pointwise jump shift. The result identifies the integral shift as the compensated positive quadratic integral plus θ times the finite drift correction, isolating the measure-level step needed to prove the full Gaussian Lévy–Khintchine exponent. Integrability hypotheses must be established separately for a spectrally negative Lévy measure.
-- source:
--   Proved gaussian_levy_esscher_shift_algebra; exact Mathlib integral_sub, integral_congr_ae, integral_add, integral_const_mul, Integrable.const_mul.

import Mathlib
open MeasureTheory

theorem AvramDividend.Classical.gaussian_esscher_jump_integral_shift
    (μ : Measure ℝ) (φ θ : ℝ) (k : ℝ → ℝ)
    (hA : Integrable (fun z : ℝ =>
      Real.exp (-(φ + θ) * z) - 1 + (φ + θ) * k z) μ)
    (hB : Integrable (fun z : ℝ =>
      Real.exp (-φ * z) - 1 + φ * k z) μ)
    (hC : Integrable (fun z : ℝ =>
      Real.exp (-φ * z) * (Real.exp (-θ * z) - 1 + θ * z)) μ)
    (hD : Integrable (fun z : ℝ =>
      k z - z * Real.exp (-φ * z)) μ) :
    (∫ z : ℝ, Real.exp (-(φ + θ) * z) - 1 + (φ + θ) * k z ∂μ) -
      (∫ z : ℝ, Real.exp (-φ * z) - 1 + φ * k z ∂μ) =
      (∫ z : ℝ,
        Real.exp (-φ * z) * (Real.exp (-θ * z) - 1 + θ * z) ∂μ) +
      θ * (∫ z : ℝ, k z - z * Real.exp (-φ * z) ∂μ) := by sorry
