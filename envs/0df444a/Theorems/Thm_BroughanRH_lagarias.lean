-- Prove2me | Theorems.Thm_BroughanRH_lagarias
-- name    : BroughanRH.lagarias
-- status  : Open
-- author  : @liuyao
-- created : 2026-11-23T04:18:26.004996+00:00
-- url     : https://prove2.me/theorems/6555321c-40ba-40c3-b9ea-87f22f1a5bcf
-- title:
--   Lagarias’s divisor-sum inequality
-- statement:
--   For each positive integer, $\sigma(n)\le H_n+e^{H_n}\log H_n$. [Source](https://math.mit.edu/~drew/grh/ArithSolution.lean).
--
--   Lean proof using the named dependencies:
--
--   ```lean
--   by
--     exact lagarias_inequality
--   ```
-- source:
--   Kevin Broughan, Equivalents of the Riemann Hypothesis, I Thm. 7.18. https://doi.org/10.1017/9781108178228

import Mathlib

namespace BroughanRH

theorem lagarias :
    ∀ n : ℕ, 0 < n → ((ArithmeticFunction.sigma 1 n : ℕ) : ℝ) ≤ (harmonic n : ℝ) + Real.exp (harmonic n : ℝ) * Real.log (harmonic n : ℝ) := by sorry

end BroughanRH
