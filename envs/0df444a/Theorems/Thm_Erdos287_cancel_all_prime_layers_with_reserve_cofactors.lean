-- Prove2me | Theorems.Thm_Erdos287_cancel_all_prime_layers_with_reserve_cofactors
-- name    : Erdos287.cancel_all_prime_layers_with_reserve_cofactors
-- status  : Proved
-- author  : @immiq
-- created : 2026-11-26T12:09:20.844689+00:00
-- url     : https://prove2.me/theorems/6a748ba5-ccc3-4cd2-8fa2-35fb3fcccf81
-- title:
--   Reserved cofactors cancel all powers of one prime in a reciprocal sum
-- statement:
--   Let $p$ be prime and $p\nmid L$. At each exponent $1\le a\le E$, suppose at least $p-1$ distinct positive cofactors dividing $L$ are available. For every integer $A$, one can select at most $p-1$ cofactors $T_a$ per exponent so that $A/(p^EL)+\sum_{a=1}^E\sum_{c\in T_a}1/(p^a c)=K/L$ for some integer $K$.
-- source:
--   Erdős Problem 287, https://www.erdosproblems.com/287.

import Mathlib

theorem Erdos287.cancel_all_prime_layers_with_reserve_cofactors (p E L : ℕ) (A : ℤ) (S : ℕ → Finset ℕ)
    (hp : p.Prime) (hL : ¬ p ∣ L)
    (hcard : ∀ a ∈ Finset.Icc 1 E, p - 1 ≤ (S a).card)
    (hcof : ∀ a ∈ Finset.Icc 1 E, ∀ c ∈ S a, 0 < c ∧ c ∣ L) :
    ∃ T : ℕ → Finset ℕ,
      (∀ a, T a ⊆ S a ∧ (T a).card ≤ p - 1) ∧
      ∃ K : ℤ,
        (A : ℚ) / ((p : ℚ) ^ E * L) +
          (∑ a ∈ Finset.Icc 1 E, ∑ c ∈ T a, (1 : ℚ) / ((p : ℚ) ^ a * c)) =
          (K : ℚ) / L := by sorry
