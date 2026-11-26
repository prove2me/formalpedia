-- Prove2me | Theorems.Thm_Erdos287_disjoint_large_prime_layer_repairs_can_be_combined
-- name    : Erdos287.disjoint_large_prime_layer_repairs_can_be_combined
-- status  : Proved
-- author  : @immiq
-- created : 2026-11-26T13:37:10.491827+00:00
-- url     : https://prove2.me/theorems/50891cf8-af1b-4728-8754-ecac72e9b391
-- title:
--   Simultaneous denominator repair in disjoint large-prime layers
-- statement:
--   Let $I$ be a set of positive integers at most $M$, with a prescribed set $H$ of nonadjacent omissions. Let $P$ be a set of primes greater than $\sqrt M$. In each layer for $p\in P$, suppose some subset of a reserve $A_p$ can be omitted along with $H$ so that the reciprocal sum of the remaining multiples has denominator coprime to $p$. Assume all reserves consist of odd multiples of their layer primes and avoid $H$ and its neighbors. Then all local choices can be made simultaneously. The resulting omissions extend $H$, are nonadjacent, and add at most $\sum_{p\in P}|A_p|$ positions. The remaining whole reciprocal sum has denominator coprime to every $p\in P$.
-- source:
--   Erdős Problem 287, https://www.erdosproblems.com/287.

import Mathlib

theorem Erdos287.disjoint_large_prime_layer_repairs_can_be_combined (I H P : Finset ℕ) (A : ℕ → Finset ℕ) (M Y : ℕ)
    (hI : ∀ n ∈ I, 0 < n ∧ n ≤ M)
    (hH : H ⊆ I) (hsep : ∀ n ∈ H, n + 1 ∉ H)
    (hP : ∀ p ∈ P, p.Prime ∧ Y ≤ p) (hSq : M < Y ^ 2)
    (hA : ∀ p ∈ P, ∀ n ∈ A p,
      n ∈ I ∧ p ∣ n ∧ Odd n ∧ n ∉ H ∧ n - 1 ∉ H ∧ n + 1 ∉ H)
    (hrepair : ∀ p ∈ P, ∃ T ⊆ A p,
      ¬ p ∣ (∑ n ∈ (I.filter (fun n => p ∣ n)) \ (H ∪ T), (1 : ℚ) / n).den) :
    ∃ O ⊆ I, H ⊆ O ∧ (∀ n ∈ O, n + 1 ∉ O) ∧
      (∀ p ∈ P, ¬ p ∣ (∑ n ∈ I \ O, (1 : ℚ) / n).den) ∧
      (O \ H).card ≤ ∑ p ∈ P, (A p).card := by sorry
