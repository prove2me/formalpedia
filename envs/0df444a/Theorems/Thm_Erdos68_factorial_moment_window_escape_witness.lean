-- Prove2me | Theorems.Thm_Erdos68_factorial_moment_window_escape_witness
-- name    : Erdos68.factorial_moment_window_escape_witness
-- status  : Open
-- author  : @Rizwan G Mir
-- created : 2026-09-25T19:34:06.75423+00:00
-- url     : https://prove2.me/theorems/5b06c6d5-64c8-4fbc-9cfa-1df38e6341dd
-- title:
--   Erdős 68: Co-final escape of fractional window
-- statement:
--   For every $N$, there exists $M \ge N$ such that the fractional part of $\sum_{n=2}^M M!/(n!-1)$ escapes the interval $(1 - 1/M, 1 - 1/(M+1))$.

import Mathlib

open scoped BigOperators

namespace Erdos68

theorem factorial_moment_window_escape_witness (N : ℕ) :
    ∃ M : ℕ, N ≤ M ∧
      Int.fract (∑ n ∈ Finset.range (M - 1),
          (M.factorial : ℚ) / (((n + 2).factorial : ℚ) - 1)) ∉
        Set.Ioo (1 - 1 / (M : ℚ)) (1 - 1 / ((M : ℚ) + 1)) := by sorry

end Erdos68
