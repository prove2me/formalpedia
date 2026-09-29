-- Prove2me | Theorems.Thm_Erdos68_factorial_moment_partial_sum_bound
-- name    : Erdos68.factorial_moment_partial_sum_bound
-- status  : Open
-- author  : @Rizwan G Mir
-- created : 2026-09-25T19:34:01.211995+00:00
-- url     : https://prove2.me/theorems/e9569ac7-3a80-4946-b44f-53924b3faf1c
-- title:
--   Erdős 68: Fractional part tail bound for factorial moment sums
-- statement:
--   For $M \ge 3$, the fractional part of the factorial moment sum $\sum_{n=2}^M M!/(n!-1)$ cannot lie in the open window $(1 - 1/M, 1 - 1/(M+1))$.

import Mathlib

open scoped BigOperators

namespace Erdos68

theorem factorial_moment_partial_sum_bound (M : ℕ) (hM : 3 ≤ M) :
    1 - 1 / (M : ℚ) < Int.fract (∑ n ∈ Finset.range (M - 1), (M.factorial : ℚ) / (((n + 2).factorial : ℚ) - 1)) →
    Int.fract (∑ n ∈ Finset.range (M - 1), (M.factorial : ℚ) / (((n + 2).factorial : ℚ) - 1)) < 1 - 1 / ((M : ℚ) + 1) →
    False := by sorry

end Erdos68
