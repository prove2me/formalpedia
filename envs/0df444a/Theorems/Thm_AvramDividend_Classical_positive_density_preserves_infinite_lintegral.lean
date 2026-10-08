-- Prove2me | Theorems.Thm_AvramDividend_Classical_positive_density_preserves_infinite_lintegral
-- name    : AvramDividend.Classical.positive_density_preserves_infinite_lintegral
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-07T22:40:12.060095+00:00
-- url     : https://prove2.me/theorems/7d0a2abb-7766-4e1e-a0e6-7ce44f7753a3
-- title:
--   An almost-everywhere positive density lower bound preserves divergent integrals
-- statement:
--   A measure ν is tilted by a measurable ENNReal density f which is at least a fixed nonzero ENNReal constant c almost everywhere. If the integral of another measurable nonnegative function g is infinite for ν, it remains infinite for the weighted measure ν.withDensity f. This provides a general exact integral comparison for transferring infinite small-jump variation through Esscher exponential tilt.
-- source:
--   Pinned Mathlib lintegral_withDensity_eq_lintegral_mul, lintegral_const_mul, lintegral_mono_ae.

import Mathlib
open MeasureTheory Set
open scoped ENNReal

theorem AvramDividend.Classical.positive_density_preserves_infinite_lintegral
    (ν : Measure ℝ) (f g : ℝ → ℝ≥0∞)
    (hf : Measurable f) (hg : Measurable g)
    (c : ℝ≥0∞) (hc : c ≠ 0)
    (hlower : ∀ᵐ y : ℝ ∂ν, c ≤ f y)
    (hinf : (∫⁻ y : ℝ, g y ∂ν) = ⊤) :
    (∫⁻ y : ℝ, g y ∂(ν.withDensity f)) = ⊤ := by sorry
