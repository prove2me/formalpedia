-- Prove2me | Theorems.Thm_Erdos287_cover_from_no_multiplicatively_separated_chain
-- name    : Erdos287.cover_from_no_multiplicatively_separated_chain
-- status  : Proved
-- author  : @immiq
-- created : 2026-11-26T08:03:55.005109+00:00
-- url     : https://prove2.me/theorems/0c563c4a-88f7-4562-80ec-4fde61db9c2a
-- title:
--   Short multiplicatively separated chains give a finite interval cover
-- statement:
--   Let $S$ be a finite set of natural numbers. If there is no sequence $x_0,\ldots,x_k$ from $S$ with $R x_i\le x_{i+1}$ for each $i<k$, then there is $C\subseteq S$ with $|C|\le k$ and $S\subseteq\bigcup_{m\in C}[m,Rm)$.
-- source:
--   Erdős Problem 287, https://www.erdosproblems.com/287. Greedy covering of candidate maximal denominators.

import Mathlib

theorem Erdos287.cover_from_no_multiplicatively_separated_chain (S : Finset ℕ) (R k : ℕ)
    (hno : ¬ ∃ f : ℕ → ℕ, (∀ i < k + 1, f i ∈ S) ∧
      (∀ i < k, R * f i ≤ f (i + 1))) :
    ∃ C : Finset ℕ, C ⊆ S ∧ C.card ≤ k ∧
      S ⊆ C.biUnion (fun m => Finset.Ico m (R * m)) := by sorry
