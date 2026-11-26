-- Prove2me | Theorems.Thm_Erdos287_prime_layer_denominator_coprime_iff_inverse_sum_zero
-- name    : Erdos287.prime_layer_denominator_coprime_iff_inverse_sum_zero
-- status  : Proved
-- author  : @immiq
-- created : 2026-11-26T13:37:11.263966+00:00
-- url     : https://prove2.me/theorems/c89883eb-a304-432d-81f9-002609f51481
-- title:
--   Exact zero-residue criterion for a prime layer’s denominator
-- statement:
--   Let $p$ be prime and let $C$ be a finite set of positive cofactors coprime to $p$. The rational sum $\sum_{c\in C}1/(pc)$ has reduced denominator coprime to $p$ exactly when $\sum_{c\in C}c^{-1}=0$ in $\mathbb Z/p\mathbb Z$.
-- source:
--   Erdős Problem 287, https://www.erdosproblems.com/287.

import Mathlib

theorem Erdos287.prime_layer_denominator_coprime_iff_inverse_sum_zero (C : Finset ℕ) (p : ℕ) (hp : p.Prime)
    (hC : ∀ c ∈ C, 0 < c ∧ ¬ p ∣ c) :
    ¬ p ∣ (∑ c ∈ C, (1 : ℚ) / (p * c : ℕ)).den ↔
      (∑ c ∈ C, (c : ZMod p)⁻¹) = 0 := by sorry
