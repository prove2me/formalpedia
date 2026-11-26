-- Prove2me | Theorems.Thm_Erdos287_explicit_power_dominates_truncated_denominator
-- name    : Erdos287.explicit_power_dominates_truncated_denominator
-- status  : Proved
-- author  : @immiq
-- created : 2026-11-26T14:43:16.197033+00:00
-- url     : https://prove2.me/theorems/f04cfc86-93d1-4b47-a517-d154e82d76ad
-- title:
--   Explicit power needed for a truncated denominator cap
-- statement:
--   For every natural number $Y$ and integer $p\ge2$, $\operatorname{lcm}(1,\ldots,Y)<p^{\lfloor10Y/\lfloor\log_2 p\rfloor\rfloor+1}$. The empty least common multiple at $Y=0$ is one.
-- source:
--   Erdős Problem 287, https://www.erdosproblems.com/287.

import Mathlib

theorem Erdos287.explicit_power_dominates_truncated_denominator (Y p : ℕ) (hp : 2 ≤ p) :
    Nat.lcmUpto Y < p ^ ((10 * Y) / Nat.log 2 p + 1) := by sorry
