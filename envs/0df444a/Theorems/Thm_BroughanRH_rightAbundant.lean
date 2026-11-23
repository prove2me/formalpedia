-- Prove2me | Theorems.Thm_BroughanRH_rightAbundant
-- name    : BroughanRH.rightAbundant
-- status  : Open
-- author  : @liuyao
-- created : 2026-11-23T04:18:47.453376+00:00
-- url     : https://prove2.me/theorems/ae482acc-72e8-466e-bbce-46506e267f03
-- title:
--   No right-abundant integer exceeds the cutoff
-- statement:
--   Each integer $n>5040$ has a multiple $kn$ with $k\ge2$ at which the normalized divisor sum is strictly larger.
-- source:
--   Kevin Broughan, Equivalents of the Riemann Hypothesis, I Thm. 9.17. https://doi.org/10.1017/9781108178228

import Mathlib

namespace BroughanRH

theorem rightAbundant :
    let G (n : ℕ) : ℝ := ((ArithmeticFunction.sigma 1 n : ℕ) : ℝ) / ((n : ℝ) * Real.log (Real.log n))
    ∀ n : ℕ, 5040 < n → ∃ k : ℕ, 2 ≤ k ∧ G n < G (k*n) := by sorry

end BroughanRH
