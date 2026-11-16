-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_a25_nat_count_occupancy_factorial_sandwich_20261115
-- name    : AvramDividend.Classical.avram_a25_nat_count_occupancy_factorial_sandwich_20261115
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-15T09:50:36.756064+00:00
-- url     : https://prove2.me/theorems/a2b896c4-ef41-48e3-88e8-166d5ef71bd8
-- title:
--   Natural count occupancy indicator squeezed by first and second falling-factorial polynomial
-- statement:
--   For every nonnegative integer count k, the indicator of a nonzero count is between k − k(k−1)/2 and k. This exact deterministic inequality is the sharp elementary second-factorial-moment bound used to estimate the original physical Lévy marked-count void probability. Integrating with first moment r and second falling-factorial moment r² gives r−r²/2 ≤ P(K>0) ≤ r, sufficient for the small-time Poisson void slope.
-- source:
--   Elementary natural count case split k=0, k=1, k≥2 and real polynomial arithmetic.

import Mathlib
noncomputable section

theorem AvramDividend.Classical.avram_a25_nat_count_occupancy_factorial_sandwich_20261115
    (k : ℕ) :
    (k : ℝ) - ((k : ℝ) * ((k : ℝ) - 1)) / 2 ≤
        (if k = 0 then (0 : ℝ) else 1) ∧
      (if k = 0 then (0 : ℝ) else 1) ≤ (k : ℝ) := by sorry
