-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_a25_nat_twojump_indicator_le_half_factorial_20261115
-- name    : AvramDividend.Classical.avram_a25_nat_twojump_indicator_le_half_factorial_20261115
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-15T15:02:37.299846+00:00
-- url     : https://prove2.me/theorems/ed69e823-6083-4582-94fe-b620d9dc16d4
-- title:
--   A two-jump occupancy indicator is bounded by half the second descending factorial
-- statement:
--   For every nonnegative integer k, the indicator of at least two points is bounded above by the number of ordered distinct point pairs divided by two. For k≥2, k(k−1)≥2; otherwise both sides are zero. The inequality enables a precise physical Borel negative-jump collision probability bound from the source second factorial count moment, supporting a Bernoulli-cell approximation to the Poisson law.
-- source:
--   Elementary natural case split and real arithmetic; physical point process second factorial moment 6d1258a3 provides the later stochastic application.

import Mathlib
noncomputable section

theorem AvramDividend.Classical.avram_a25_nat_twojump_indicator_le_half_factorial_20261115
    (k : ℕ) :
    (if 2 ≤ k then (1 : ℝ) else 0) ≤
      ((k : ℝ) * ((k : ℝ) - 1)) / 2 := by sorry
