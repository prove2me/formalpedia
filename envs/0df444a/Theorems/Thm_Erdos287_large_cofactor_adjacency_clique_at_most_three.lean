-- Prove2me | Theorems.Thm_Erdos287_large_cofactor_adjacency_clique_at_most_three
-- name    : Erdos287.large_cofactor_adjacency_clique_at_most_three
-- status  : Proved
-- author  : @immiq
-- created : 2026-11-26T13:50:38.045289+00:00
-- url     : https://prove2.me/theorems/fcc85268-cfc9-43a7-9f01-67bc9ca00f0d
-- title:
--   No four mutually adjacent large-factor layers in a dense interval
-- statement:
--   Let $P$ be a collection of natural numbers exceeding $3B^2$. Suppose every pair of distinct members of $P$ has consecutive multiples in $[m,M]$, with both cofactors positive and at most $B$. If $m>0$, $M\ge2$, and $M<3m$, then $|P|\le3$.
-- source:
--   Erdős Problem 287, https://www.erdosproblems.com/287.

import Mathlib

theorem Erdos287.large_cofactor_adjacency_clique_at_most_three (P : Finset ℕ) (a : ℕ → ℕ → ℕ) (m M B : ℕ)
    (hm : 0 < m) (hM : 2 ≤ M) (hRatio : M < 3 * m)
    (hP : ∀ p ∈ P, 3 * B ^ 2 < p)
    (hA : ∀ p ∈ P, ∀ q ∈ P, p ≠ q →
      0 < a p q ∧ a p q ≤ B ∧ m ≤ a p q * p ∧ a p q * p ≤ M)
    (hE : ∀ p ∈ P, ∀ q ∈ P, p ≠ q →
      a p q * p + 1 = a q p * q ∨ a q p * q + 1 = a p q * p) :
    P.card ≤ 3 := by sorry
