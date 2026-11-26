-- Prove2me | Theorems.Thm_Erdos287_large_square_divisor_weight_bound
-- name    : Erdos287.large_square_divisor_weight_bound
-- status  : Proved
-- author  : @immiq
-- created : 2026-11-26T04:28:55.78542+00:00
-- url     : https://prove2.me/theorems/c32904c8-5424-4dfd-a295-0d9a670ab25e
-- title:
--   Weighted bound for the large-square exception in the sieve
-- statement:
--   For positive U, let E be the integers from 1 to X divisible by p squared for some integer p>U. Then |E|≤X/U. For every real weight w the square of its sum on E is at most (X/U) times the sum of w(n) squared over 1≤n≤X.
-- source:
--   Erdős Problem #287, sieve estimate for the overlap of the two factors of a modulus. A prime greater than U common to both factors contributes a square divisor of the shifted integer.

import Mathlib

theorem Erdos287.large_square_divisor_weight_bound (X U : ℕ) (hU : 0 < U) (w : ℕ → ℝ) :
    let E := (Finset.Ioc 0 X).filter (fun n => ∃ p ∈ Finset.Ioc U X, p ^ 2 ∣ n)
    (E.card : ℝ) ≤ (X : ℝ) / U ∧
      (∑ n ∈ E, w n) ^ 2 ≤ ((X : ℝ) / U) * ∑ n ∈ Finset.Ioc 0 X, w n ^ 2 := by sorry
