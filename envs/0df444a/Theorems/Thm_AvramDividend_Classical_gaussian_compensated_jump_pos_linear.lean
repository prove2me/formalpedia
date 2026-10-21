-- Prove2me | Theorems.Thm_AvramDividend_Classical_gaussian_compensated_jump_pos_linear
-- name    : AvramDividend.Classical.gaussian_compensated_jump_pos_linear
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-20T23:00:19.516785+00:00
-- url     : https://prove2.me/theorems/f42f0283-bc34-44cc-a9f3-00f34930d3b0
-- title:
--   Positivity and linear upper bound for the negative-jump exponential compensator
-- statement:
--   For nonnegative θ and negative-jump magnitude z≥0, the compensated jump factor exp(−θz)−1+θz is nonnegative and no greater than θz. The lower inequality follows from the exponential tangent line; the upper follows from monotonicity exp(−u)≤1. This is the positive-ENNReal and large-jump component of the Gaussian double-tail Lévy–Khintchine transform, with the small-jump quadratic integrability estimate still to prove.
-- source:
--   Pinned Mathlib Real.add_one_le_exp and exponential monotonicity.

import Mathlib

theorem AvramDividend.Classical.gaussian_compensated_jump_pos_linear
    (θ z : ℝ) (hθ : 0 ≤ θ) (hz : 0 ≤ z) :
    0 ≤ Real.exp (-θ * z) - 1 + θ * z ∧
      Real.exp (-θ * z) - 1 + θ * z ≤ θ * z := by sorry
