-- Prove2me | Theorems.Thm_BroughanRH_extremelyAbundant
-- name    : BroughanRH.extremelyAbundant
-- status  : Open
-- author  : @liuyao
-- created : 2026-11-23T04:18:57.522938+00:00
-- url     : https://prove2.me/theorems/ff5709d6-ce21-43fe-b536-fc38c3b2f21a
-- title:
--   Infinitely many extremely abundant numbers
-- statement:
--   There are infinitely many strict record values of the normalized divisor sum starting at $10080$.
-- source:
--   Kevin Broughan, Equivalents of the Riemann Hypothesis, I Thm. 9.22. https://doi.org/10.1017/9781108178228

import Mathlib

namespace BroughanRH

theorem extremelyAbundant :
    let G (n : ℕ) : ℝ := ((ArithmeticFunction.sigma 1 n : ℕ) : ℝ) / ((n : ℝ) * Real.log (Real.log n))
    Set.Infinite {n : ℕ | 10080 ≤ n ∧ ∀ m : ℕ, 10080 ≤ m → m < n → G m < G n} := by sorry

end BroughanRH
