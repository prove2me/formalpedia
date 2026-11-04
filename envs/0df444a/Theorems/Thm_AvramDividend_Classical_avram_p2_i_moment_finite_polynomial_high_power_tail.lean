-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p2_i_moment_finite_polynomial_high_power_tail
-- name    : AvramDividend.Classical.avram_p2_i_moment_finite_polynomial_high_power_tail
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T17:18:25.61047+00:00
-- url     : https://prove2.me/theorems/eddfc673-1a44-4a29-a70f-506eb953e70f
-- title:
--   Uniform high-power tail domination for a finite polynomial
-- statement:
--   For a real finite polynomial represented by coefficients on a finite subset of degrees bounded by n, and every real z at least 2, multiplying its absolute value by 2 to the power r is bounded by the sum of absolute coefficients times z to the power n+r. This is the quantitative high-moment tail bound needed to transfer moment convergence to compact continuous tests when approximating positive measures can have mass above 1. It assumes no target convergence.

import Mathlib
open scoped BigOperators

theorem AvramDividend.Classical.avram_p2_i_moment_finite_polynomial_high_power_tail
    (s : Finset ℕ) (a : ℕ → ℝ) (n r : ℕ)
    (hs : ∀ j ∈ s, j ≤ n) (z : ℝ) (hz : 2 ≤ z) :
    (2 : ℝ) ^ r * |∑ j ∈ s, a j * z ^ j| ≤
      (∑ j ∈ s, |a j|) * z ^ (n + r) := by sorry
