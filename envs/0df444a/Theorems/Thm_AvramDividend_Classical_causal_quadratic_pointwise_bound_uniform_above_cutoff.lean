-- Prove2me | Theorems.Thm_AvramDividend_Classical_causal_quadratic_pointwise_bound_uniform_above_cutoff
-- name    : AvramDividend.Classical.causal_quadratic_pointwise_bound_uniform_above_cutoff
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-23T15:15:05.727115+00:00
-- url     : https://prove2.me/theorems/d6684516-77ef-4404-9234-c117bb1d3736
-- title:
--   Uniform quadratic-geometric causal power bound away from the origin
-- statement:
--   A quadratic-geometric pointwise estimate F_n(x) ≤ A_n/x on the positive half-line becomes a uniform bound F_n(x) ≤ A_n/δ for every x≥δ>0. This prepares the Weierstrass-M uniform convergence argument on Gaussian scale-function compact intervals away from zero.
-- source:
--   Monotonicity of division by positive denominators, since δ≤x and the geometric coefficient is nonnegative.

import Mathlib.Analysis.Convolution
import Mathlib.Tactic.Positivity

open MeasureTheory Set

theorem AvramDividend.Classical.causal_quadratic_pointwise_bound_uniform_above_cutoff
    (F : ℕ → ℝ → ℝ) (ρ : ℝ) (hρ : 0 ≤ ρ)
    (hpoint : ∀ n : ℕ, ∀ x : ℝ, 0 < x →
      F n x ≤ ((n + 1 : ℝ) ^ 2 * ρ ^ (n + 1)) / x) :
    ∀ δ : ℝ, 0 < δ → ∀ n : ℕ, ∀ x : ℝ, δ ≤ x →
      F n x ≤ ((n + 1 : ℝ) ^ 2 * ρ ^ (n + 1)) / δ := by sorry
