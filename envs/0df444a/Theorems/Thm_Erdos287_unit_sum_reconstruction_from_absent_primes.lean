-- Prove2me | Theorems.Thm_Erdos287_unit_sum_reconstruction_from_absent_primes
-- name    : Erdos287.unit_sum_reconstruction_from_absent_primes
-- status  : Proved
-- author  : @immiq
-- created : 2026-11-26T12:51:54.199056+00:00
-- url     : https://prove2.me/theorems/2105a7a5-9777-5293-a72b-0f7f494d02aa
-- title:
--   Exact reconstruction of a unit-fraction sum from absent prime residues
-- statement:
--   Let the denominators in $D$ all divide a positive integer $L$, let $W=\sum_{n\in D}L/n$, and let $P$ be a finite set of primes not dividing $L$. If $|W-L|<\prod_{p\in P}p$, then the rational reciprocal sum equals one exactly when its modular inverse sum equals one for every $p\in P$.
-- source:
--   Erdős Problem 287, https://www.erdosproblems.com/287.

import Mathlib

theorem Erdos287.unit_sum_reconstruction_from_absent_primes (D P : Finset ℕ) (L : ℕ) (hL : 0 < L)
    (hD : ∀ n ∈ D, n ∣ L) (hP : ∀ p ∈ P, p.Prime ∧ ¬ p ∣ L)
    (hbound : Int.natAbs (((∑ n ∈ D, L / n : ℕ) : ℤ) - L) < ∏ p ∈ P, p) :
    (∑ n ∈ D, (1 : ℚ) / n) = 1 ↔
      ∀ p ∈ P, (∑ n ∈ D, (n : ZMod p)⁻¹) = 1 := by sorry
