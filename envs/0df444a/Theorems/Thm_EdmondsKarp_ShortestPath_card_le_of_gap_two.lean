-- Prove2me | Theorems.Thm_EdmondsKarp_ShortestPath_card_le_of_gap_two
-- name    : EdmondsKarp.ShortestPath.card_le_of_gap_two
-- status  : Proved
-- author  : @arexychen
-- created : 2026-10-02T20:14:59.477895+00:00
-- url     : https://prove2.me/theorems/594772d7-8ad5-4319-80f6-5144c83b97e3
-- title:
--   Counting an ordered set whose values grow by at least two
-- statement:
--   For a finite set of natural-number indices and a natural-valued function bounded strictly by n on that set, if values increase by at least two between any two increasing indices, then twice the set cardinality is at most n+1.
-- source:
--   Auxiliary counting and iteration lemmas for Edmonds and Karp (1972), §1.2 p. 252. DOI: 10.1145/321694.321699.

import Mathlib

theorem EdmondsKarp.ShortestPath.card_le_of_gap_two (S : Finset ℕ) (d : ℕ → ℕ) (n : ℕ)
    (hbound : ∀ k ∈ S, d k < n)
    (hgap : ∀ k ∈ S, ∀ l ∈ S, k < l → d k + 2 ≤ d l) :
    2 * S.card ≤ n + 1 := by sorry
