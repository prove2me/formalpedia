-- Prove2me | Theorems.Thm_Erdos287_log_ratio_lower_bound_from_omissions
-- name    : Erdos287.log_ratio_lower_bound_from_omissions
-- status  : Proved
-- author  : @immiq
-- created : 2026-11-26T05:46:17.172546+00:00
-- url     : https://prove2.me/theorems/d5c17c5b-e9c1-4d82-b340-c0f1743c94b0
-- title:
--   An omitted reciprocal sum increases the required denominator ratio
-- statement:
--   Let m and M be the smallest and largest denominators of an increasing unit-fraction representation of 1. If H consists of known omitted integers in the interval, then 1 plus their reciprocal sum is at most log(M/(m−1)).
-- source:
--   Erdős Problem #287. The harmonic upper envelope for the disjoint union of denominators and certified omissions.

import Mathlib

theorem Erdos287.log_ratio_lower_bound_from_omissions (k : ℕ) (hk : 2 ≤ k) (f : ℕ → ℕ)
    (hmin : 1 < f 0)
    (hmono : ∀ i j, i < j → j < k → f i < f j)
    (hsum : ∑ i ∈ Finset.range k, (1 : ℚ) / f i = 1)
    (H : Finset ℕ)
    (hH : ∀ n ∈ H, f 0 ≤ n ∧ n ≤ f (k - 1))
    (hmiss : ∀ i, i < k → f i ∉ H) :
    (1 : ℝ) + ∑ n ∈ H, (1 : ℝ) / n ≤
      Real.log ((f (k - 1) : ℝ) / ((f 0 - 1 : ℕ) : ℝ)) := by sorry
