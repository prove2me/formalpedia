-- Prove2me | Theorems.Thm_BroughanRH_kaneko
-- name    : BroughanRH.kaneko
-- status  : Open
-- author  : @liuyao
-- created : 2026-11-23T04:18:29.56388+00:00
-- url     : https://prove2.me/theorems/9aa8afb5-50d8-410f-a224-ad0cbb9c9c8e
-- title:
--   Kaneko’s divisor-sum inequality
-- statement:
--   For each integer $n>60$, the divisor sum is at most $e^{H_n}\log H_n$.
-- source:
--   Kevin Broughan, Equivalents of the Riemann Hypothesis, I §7.10. https://doi.org/10.1017/9781108178228

import Mathlib

namespace BroughanRH

theorem kaneko :
    ∀ n : ℕ, 60 < n → ((ArithmeticFunction.sigma 1 n : ℕ) : ℝ) ≤ Real.exp (harmonic n : ℝ) * Real.log (harmonic n : ℝ) := by sorry

end BroughanRH
