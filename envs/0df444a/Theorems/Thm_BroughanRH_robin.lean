-- Prove2me | Theorems.Thm_BroughanRH_robin
-- name    : BroughanRH.robin
-- status  : Open
-- author  : @liuyao
-- created : 2026-11-23T04:18:20.057194+00:00
-- url     : https://prove2.me/theorems/1715a61f-73dd-47b4-b170-7ac4574d8a97
-- title:
--   Robin’s divisor-sum inequality
-- statement:
--   For all integers $n>5040$, the sum of the positive divisors is strictly below $e^\gamma n\log\log n$. [Source](https://math.mit.edu/~drew/grh/ArithSolution.lean).
--
--   Lean proof using the named dependencies:
--
--   ```lean
--   by
--     exact robin_inequality
--   ```
-- source:
--   Kevin Broughan, Equivalents of the Riemann Hypothesis, I Thm. 7.16. https://doi.org/10.1017/9781108178228

import Mathlib

namespace BroughanRH

theorem robin :
    ∀ n : ℕ, 5040 < n → ((ArithmeticFunction.sigma 1 n : ℕ) : ℝ) < Real.exp Real.eulerMascheroniConstant * n * Real.log (Real.log n) := by sorry

end BroughanRH
