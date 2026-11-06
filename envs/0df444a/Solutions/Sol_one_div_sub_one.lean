-- Prove2me | solution 1 for one_div_sub_one
-- status  : ACCEPTED   (prove)
-- author  : @nonlocally
-- created : 2026-11-05T23:03:57.530373+00:00
-- url     : https://prove2.me/submissions/95947b0f-688a-4333-9310-6a5676aa2886

import Mathlib.Analysis.SumIntegralComparisons

theorem solution (n : ℕ) : 1 / (↑(n - 1) : ℝ) ≤ 2 / n := by
  by_cases hn : n ≤ 1
  · interval_cases n <;> norm_num
  · have hn2 : 2 ≤ n := by omega
    have hpos₁ : (0 : ℝ) < (↑(n - 1) : ℝ) := by
      exact_mod_cast (Nat.sub_pos_of_lt (by omega : 1 < n))
    have hpos₂ : (0 : ℝ) < (n : ℝ) := by
      exact_mod_cast (by omega : 0 < n)
    have hn2' : (2 : ℝ) ≤ n := by exact_mod_cast hn2
    rw [div_le_div_iff₀ hpos₁ hpos₂, Nat.cast_sub (by omega : 1 ≤ n)]
    norm_num
    nlinarith
