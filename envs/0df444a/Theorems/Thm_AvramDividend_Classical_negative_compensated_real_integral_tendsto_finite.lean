-- Prove2me | Theorems.Thm_AvramDividend_Classical_negative_compensated_real_integral_tendsto_finite
-- name    : AvramDividend.Classical.negative_compensated_real_integral_tendsto_finite
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-06T22:35:14.489049+00:00
-- url     : https://prove2.me/theorems/c02c41f4-3139-4450-a879-ef89143348a4
-- title:
--   Finite negative-jump first moment gives convergence of normalised real exponential integral
-- statement:
--   For a measure supported on negative jumps with an integrable absolute first moment, the real Bochner integrals of the normalised compensated exponential kernel at θ=n+1 converge to the first absolute moment, assuming integrability at each integer θ. Converts the full infinite-measure extended monotone-convergence theorem to a finite real limit, supporting the bounded-variation positive-drift branch of the Lévy exponent asymptotics.
-- source:
--   The same Prove2Me negative_compensated_lintegral_tendsto and pinned Mathlib ofReal_integral_eq_lintegral_ofReal, ENNReal.tendsto_toReal at finite non-top endpoints and ENNReal.toReal_ofReal.

import Mathlib

open MeasureTheory Filter

theorem AvramDividend.Classical.negative_compensated_real_integral_tendsto_finite
    (ν : Measure ℝ) (hneg : ∀ᵐ y ∂ν, y < 0)
    (hA : Integrable (fun y : ℝ => |y|) ν)
    (hint : ∀ n : ℕ, Integrable (fun y : ℝ =>
      (Real.exp (((n : ℝ) + 1) * y) - 1 -
        ((n : ℝ) + 1) * y) / ((n : ℝ) + 1)) ν) :
    Tendsto (fun n : ℕ =>
      ∫ y : ℝ, (Real.exp (((n : ℝ) + 1) * y) - 1 -
        ((n : ℝ) + 1) * y) / ((n : ℝ) + 1) ∂ν)
      atTop (nhds (∫ y : ℝ, |y| ∂ν)) := by sorry
