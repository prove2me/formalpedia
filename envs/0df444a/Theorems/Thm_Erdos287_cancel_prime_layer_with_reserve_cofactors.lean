-- Prove2me | Theorems.Thm_Erdos287_cancel_prime_layer_with_reserve_cofactors
-- name    : Erdos287.cancel_prime_layer_with_reserve_cofactors
-- status  : Proved
-- author  : @immiq
-- created : 2026-11-26T06:42:46.482875+00:00
-- url     : https://prove2.me/theorems/81c77e47-6cb2-5283-b010-d6ae33e9ba18
-- title:
--   Reserved cofactors cancel one prime-power layer of a reciprocal sum
-- statement:
--   Let $p$ be prime, $e\ge1$, $A$ an integer, and $L$ not divisible by $p$. Suppose a finite set $S$ of at least $p-1$ positive cofactors all divide $L$. There exists $T\subseteq S$ with $|T|\le p-1$ and an integer $K$ such that
--
--   $$\frac{A}{p^eL}+\sum_{c\in T}\frac1{p^ec}=\frac{K}{p^{e-1}L}.$$
--
--   Thus a reserve of available denominators at valuation $e$ can clear one layer of the $p$-part of a reciprocal sum.
-- source:
--   Erdős Problem 287, https://www.erdosproblems.com/287. A Cauchy–Davenport cofactor correction for a prescribed prime-power layer.

import Mathlib

theorem Erdos287.cancel_prime_layer_with_reserve_cofactors (p e L : ℕ) (A : ℤ) (S : Finset ℕ) (hp : p.Prime) (he : 1 ≤ e)
    (hL : ¬ p ∣ L) (hcard : p - 1 ≤ S.card) (hcof : ∀ c ∈ S, 0 < c ∧ c ∣ L) :
    ∃ T ⊆ S, T.card ≤ p - 1 ∧ ∃ K : ℤ,
      (A : ℚ) / ((p : ℚ) ^ e * L) + (∑ c ∈ T, (1 : ℚ) / ((p : ℚ) ^ e * c)) =
        (K : ℚ) / ((p : ℚ) ^ (e - 1) * L) := by sorry
