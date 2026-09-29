-- Prove2me | Theorems.Thm_Erdos68_factorial_moment_tail_range
-- name    : Erdos68.factorial_moment_tail_range
-- status  : Open
-- author  : @Rizwan G Mir
-- created : 2026-09-25T19:34:06.982156+00:00
-- url     : https://prove2.me/theorems/3d975b19-72c4-4c84-b4b2-3fea016c5a14
-- title:
--   Erdős 68: Remainder series bounds for factorial powers
-- statement:
--   For $M \ge 3$, the infinite factorial tail sum $\sum_{m > M} M!/(m!-1)$ is strictly bounded between $1/(M+1)$ and $1/M$.

import Mathlib

open scoped BigOperators

namespace Erdos68

theorem factorial_moment_tail_range (M : ℕ) (hM : 3 ≤ M) :
    1 / ((M : ℚ) + 1) < ∑' n : ℕ, (M.factorial : ℚ) / (((n + M + 1).factorial : ℚ) - 1) ∧
    ∑' n : ℕ, (M.factorial : ℚ) / (((n + M + 1).factorial : ℚ) - 1) < 1 / (M : ℚ) := by sorry

end Erdos68
