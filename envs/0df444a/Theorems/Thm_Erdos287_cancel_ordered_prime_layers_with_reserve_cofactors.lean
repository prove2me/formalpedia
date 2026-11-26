-- Prove2me | Theorems.Thm_Erdos287_cancel_ordered_prime_layers_with_reserve_cofactors
-- name    : Erdos287.cancel_ordered_prime_layers_with_reserve_cofactors
-- status  : Proved
-- author  : @immiq
-- created : 2026-11-26T12:13:15.266857+00:00
-- url     : https://prove2.me/theorems/23992c53-058f-4a15-a5c5-060c7e700d3d
-- title:
--   Simultaneous reciprocal carries for an ordered list of primes
-- statement:
--   Let $x$ be a rational whose denominator divides $Q>0$. For every prime $p$ in a list of distinct primes, write $Q=p^{E_p}L_p$ with $p\nmid L_p$. At each $1\le a\le E_p$ give at least $p-1$ distinct positive cofactors $c\mid L_p$ as a reserve. Suppose the reserve denominators at any later prime are all coprime to each earlier prime. There are subsets of at most $p-1$ cofactors per layer for which adding the chosen reciprocals $1/(p^a c)$ to $x$ gives a rational with reduced denominator coprime to every listed prime.
-- source:
--   Erdős Problem 287, https://www.erdosproblems.com/287.

import Mathlib

theorem Erdos287.cancel_ordered_prime_layers_with_reserve_cofactors (ps : List ℕ) (Q : ℕ) (x : ℚ) (E L : ℕ → ℕ)
    (S : ℕ → ℕ → Finset ℕ) (hQ : 0 < Q) (hx : x.den ∣ Q)
    (hprime : ∀ p ∈ ps, p.Prime)
    (hsplit : ∀ p ∈ ps, p ^ E p * L p = Q ∧ ¬ p ∣ L p)
    (hcard : ∀ p ∈ ps, ∀ a ∈ Finset.Icc 1 (E p), p - 1 ≤ (S p a).card)
    (hcof : ∀ p ∈ ps, ∀ a ∈ Finset.Icc 1 (E p), ∀ c ∈ S p a, 0 < c ∧ c ∣ L p)
    (hcross : ps.Pairwise (fun p q => p ≠ q ∧
      ∀ a ∈ Finset.Icc 1 (E q), ∀ c ∈ S q a, ¬ p ∣ q ^ a * c)) :
    ∃ T : ℕ → ℕ → Finset ℕ,
      (∀ p ∈ ps, ∀ a, T p a ⊆ S p a ∧ (T p a).card ≤ p - 1) ∧
      ∀ p ∈ ps, ¬ p ∣ (x + (ps.map (fun q =>
        ∑ a ∈ Finset.Icc 1 (E q), ∑ c ∈ T q a, (1 : ℚ) / ((q : ℚ) ^ a * c))).sum).den := by sorry
