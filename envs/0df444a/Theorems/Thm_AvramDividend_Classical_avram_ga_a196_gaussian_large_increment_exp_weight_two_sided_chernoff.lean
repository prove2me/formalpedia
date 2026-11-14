-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ga_a196_gaussian_large_increment_exp_weight_two_sided_chernoff
-- name    : AvramDividend.Classical.avram_ga_a196_gaussian_large_increment_exp_weight_two_sided_chernoff
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-13T17:16:30.534733+00:00
-- url     : https://prove2.me/theorems/24310e13-63b5-476a-990b-832288dfb764
-- title:
--   Gaussian large-increment exponential weighted tail dominated by two Esscher shifts
-- statement:
--   For any real centred Gaussian source increment z, any exponential weight θ, nonnegative Chernoff rate r and nonnegative threshold η, the exponential e^(θ z) restricted to |z| at least η is bounded pointwise by e^(-r η) times the sum of the two exponential tilts e^((θ+r)z) and e^((θ-r)z). This gives directly integrable exponentially decaying expected Gaussian large-increment tails from original pinned MGF lemmas, supporting the positive Taylor source a149.
-- source:
--   Elementary exponential order comparison on positive and negative Gaussian tails, split at z=0.

import Mathlib
open Real
noncomputable section

theorem AvramDividend.Classical.avram_ga_a196_gaussian_large_increment_exp_weight_two_sided_chernoff
    (θ r η z : ℝ) (hr : 0 ≤ r) (hη : 0 ≤ η) :
    (if η ≤ |z| then Real.exp (θ * z) else 0) ≤
      Real.exp (-r * η) *
        (Real.exp ((θ + r) * z) + Real.exp ((θ - r) * z)) := by sorry
