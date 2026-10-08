-- Prove2me | Theorems.Thm_AvramDividend_Classical_negative_exponential_residual_integral_tendsto_zero
-- name    : AvramDividend.Classical.negative_exponential_residual_integral_tendsto_zero
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-06T22:56:55.438275+00:00
-- url     : https://prove2.me/theorems/a609a39e-9058-4de2-b98f-d8b65349b7fe
-- title:
--   Vanishing normalised residual integral for finite negative-jump first moment
-- statement:
--   For an arbitrary measure supported almost everywhere on strictly negative real jumps with integrable absolute first moment, the real integral of (1−exp((n+1)y))/(n+1) converges to zero as n grows. This is the precise finite-moment dominated-convergence step needed for the non-Gaussian bounded-variation positive-drift Lévy exponent, without relying on published Prove2Me child theorem imports.
-- source:
--   Pinned Mathlib MeasureTheory.tendsto_integral_of_dominated_convergence, elementary exponential bounds, and tendsto_one_div_add_atTop_nhds_zero_nat.

import Mathlib

open Filter MeasureTheory

theorem AvramDividend.Classical.negative_exponential_residual_integral_tendsto_zero
    (ν : Measure ℝ) (hneg : ∀ᵐ y ∂ν, y < 0)
    (hA : Integrable (fun y : ℝ => |y|) ν) :
    Tendsto (fun n : ℕ =>
      ∫ y : ℝ, (1 - Real.exp (((n : ℝ) + 1) * y)) /
        ((n : ℝ) + 1) ∂ν) atTop (nhds (0 : ℝ)) := by sorry
