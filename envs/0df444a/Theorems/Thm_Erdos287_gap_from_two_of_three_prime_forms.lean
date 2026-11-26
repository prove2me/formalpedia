-- Prove2me | Theorems.Thm_Erdos287_gap_from_two_of_three_prime_forms
-- name    : Erdos287.gap_from_two_of_three_prime_forms
-- status  : Proved
-- author  : @immiq
-- created : 2026-11-26T03:30:28.576165+00:00
-- url     : https://prove2.me/theorems/a9c7d2b1-7e23-53c6-8a5d-ed83d3703a95
-- title:
--   Two of three explicit prime forms force a denominator gap
-- statement:
--   Let $1<n_0<\cdots<n_{k-1}=M$ have reciprocal sum one. Suppose there is an integer $t\ge 5$ such that
--
--   $$24t+4\le M\le29t$$
--
--   and at least two of $6t+1,8t+1,12t+1$ are prime. Then some consecutive denominator gap is at least three.
-- source:
--   Erdős Problem 287, https://www.erdosproblems.com/287. Builds on Erdos287.prime_power_pair_excludes_band.

import Mathlib

theorem Erdos287.gap_from_two_of_three_prime_forms (k : ℕ) (hk : 2 ≤ k) (f : ℕ → ℕ)
    (hf1 : ∀ i, i < k → 1 < f i)
    (hmono : ∀ i j, i < j → j < k → f i < f j)
    (hsum : ∑ i ∈ Finset.range k, (1 : ℚ) / f i = 1)
    (t : ℕ) (ht : 5 ≤ t)
    (hlo : 24 * t + 4 ≤ f (k - 1)) (hhi : f (k - 1) ≤ 29 * t)
    (hprime : (Nat.Prime (6 * t + 1) ∧ Nat.Prime (8 * t + 1)) ∨
      (Nat.Prime (6 * t + 1) ∧ Nat.Prime (12 * t + 1)) ∨
      (Nat.Prime (8 * t + 1) ∧ Nat.Prime (12 * t + 1))) :
    ∃ i, i + 1 < k ∧ 3 ≤ f (i + 1) - f i := by sorry
