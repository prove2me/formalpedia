-- Prove2me | Theorems.Thm_Erdos287_prime_neighbor_support_for_unit_reciprocal_sums
-- name    : Erdos287.prime_neighbor_support_for_unit_reciprocal_sums
-- status  : Proved
-- author  : @immiq
-- created : 2026-11-26T08:51:55.0907+00:00
-- url     : https://prove2.me/theorems/dd260b6b-c4ed-5d7d-829b-b3df0dbeb4e0
-- title:
--   Redundant denominator divisibility and forced neighbors of large primes
-- statement:
--   Let $D$ be a set of positive denominators in $[\ell,h]$ with reciprocal sum one and at least one member of every consecutive pair in that interval. Every $n\in D$ divides the least common multiple of $D\setminus\{n\}$. Consequently, a prime $p$ with $2p>h$ cannot belong to $D$, and every immediate neighbor of $p$ belonging to a consecutive pair with $p$ in $[\ell,h]$ must lie in $D$.
-- source:
--   Erdős Problem 287, https://www.erdosproblems.com/287. Analytic application uses Thorner and Zaman, Refinements to the prime number theorem for arithmetic progressions, Theorem 1.1 and Eq. (1.7), https://arxiv.org/pdf/2108.10878.

import Mathlib

theorem Erdos287.prime_neighbor_support_for_unit_reciprocal_sums (D : Finset ℕ) (lo hi : ℕ) (hlo : 0 < lo)
    (hD : D ⊆ Finset.Icc lo hi) (hsum : ∑ n ∈ D, (1 : ℚ) / n = 1)
    (hcover : ∀ n, lo ≤ n → n + 1 ≤ hi → n ∈ D ∨ (n + 1) ∈ D) :
    (∀ n ∈ D, n ∣ (D.erase n).lcm id) ∧
    (∀ p : ℕ, p.Prime → hi < 2 * p →
      p ∉ D ∧ (lo ≤ p - 1 → p ≤ hi → p - 1 ∈ D) ∧
        (lo ≤ p → p + 1 ≤ hi → p + 1 ∈ D)) := by sorry
