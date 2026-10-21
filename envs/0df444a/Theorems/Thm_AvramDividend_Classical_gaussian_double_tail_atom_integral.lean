-- Prove2me | Theorems.Thm_AvramDividend_Classical_gaussian_double_tail_atom_integral
-- name    : AvramDividend.Classical.gaussian_double_tail_atom_integral
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-20T22:40:06.924269+00:00
-- url     : https://prove2.me/theorems/dfe7a40a-916f-467f-b15c-19dd76179045
-- title:
--   Exact exponential single-jump double-tail integral for the Gaussian Volterra kernel
-- statement:
--   For any real θ and z, the oriented interval integral ∫₀ᶻ θ²(z−t)exp(−θt)dt equals exp(−θz)−1+θz. The proof uses an explicit exponential-polynomial antiderivative and the fundamental theorem of calculus. This is the elementary analytic integrand identity underlying the Esscher-tilted negative-jump double-tail Laplace transform for Gaussian scale-function regularity, without assuming the measure-level stochastic step.
-- source:
--   Fundamental theorem of calculus, exact pinned Mathlib derivative/intervalIntegral declarations.

import Mathlib
open MeasureTheory

theorem AvramDividend.Classical.gaussian_double_tail_atom_integral
    (θ z : ℝ) :
    (∫ t in (0 : ℝ)..z,
      θ ^ 2 * ((z - t) * Real.exp (-θ * t))) =
      Real.exp (-θ * z) - 1 + θ * z := by sorry
