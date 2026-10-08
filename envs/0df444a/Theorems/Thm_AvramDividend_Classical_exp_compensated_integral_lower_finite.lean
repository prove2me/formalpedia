-- Prove2me | Theorems.Thm_AvramDividend_Classical_exp_compensated_integral_lower_finite
-- name    : AvramDividend.Classical.exp_compensated_integral_lower_finite
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-06T20:24:09.339985+00:00
-- url     : https://prove2.me/theorems/f9d55a73-bb40-4d36-b725-588293d5bd31
-- title:
--   Integrated compensated exponential lower bound on a finite negative-jump measure
-- statement:
--   For a finite measure supported on nonpositive real jumps, with integrable jump size and any nonnegative Laplace parameter, the integral of the compensated exponential kernel is bounded below by the integral of theta times absolute jump size minus one. Applying this to a finite truncated Lévy jump measure gives the uniform lower estimate L(theta)/theta ≥ A_epsilon−N_epsilon/theta needed to show eventual exponent growth in the infinite small-jump first-moment non-Gaussian branch.
-- source:
--   Lévy–Khintchine compensated jump kernel and the elementary nonnegativity of exp(theta*y), applied on a truncated finite-mass negative-jump region. This bound is a source-faithful analytic dependency of AvramDividend.Classical.scaleFunction_strict_pos_of_standing.

import Mathlib

open MeasureTheory Set

theorem AvramDividend.Classical.exp_compensated_integral_lower_finite
    (ν : Measure ℝ) [IsFiniteMeasure ν]
    (θ : ℝ) (hθ : 0 ≤ θ)
    (hneg : ∀ᵐ y ∂ν, y ≤ 0)
    (hyint : Integrable (fun y : ℝ => y) ν) :
    (∫ y : ℝ, θ * |y| - 1 ∂ν) ≤
      ∫ y : ℝ, (Real.exp (θ * y) - 1 - θ * y) ∂ν := by sorry
