-- Prove2me | Theorems.Thm_BroughanRH_extraordinary
-- name    : BroughanRH.extraordinary
-- status  : Open
-- author  : @liuyao
-- created : 2026-11-23T04:18:39.149939+00:00
-- url     : https://prove2.me/theorems/cd42e290-b314-4a99-ab95-be992353e11c
-- title:
--   The unique extraordinary integer
-- statement:
--   Exactly one composite integer, $4$, maximizes the normalized divisor sum against both division by every prime factor and multiplication by every integer $k\ge2$. [Source](https://arxiv.org/abs/1112.6010).
-- source:
--   Kevin Broughan, Equivalents of the Riemann Hypothesis, I Thm. 9.8. https://doi.org/10.1017/9781108178228

import Mathlib

namespace BroughanRH

theorem extraordinary :
    let G (n : ℕ) : ℝ := ((ArithmeticFunction.sigma 1 n : ℕ) : ℝ) / ((n : ℝ) * Real.log (Real.log n))
    ∀ n : ℕ, ((1 < n ∧ ¬ n.Prime) ∧ (∀ p : ℕ, p.Prime → p ∣ n → G (n / p) ≤ G n) ∧ (∀ k : ℕ, 2 ≤ k → G (k*n) ≤ G n)) ↔ n = 4 := by sorry

end BroughanRH
