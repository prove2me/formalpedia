-- Prove2me | Theorems.Thm_Erdos287_card_bound_for_close_maximum_cluster
-- name    : Erdos287.card_bound_for_close_maximum_cluster
-- status  : Proved
-- author  : @immiq
-- created : 2026-11-26T10:45:32.944039+00:00
-- url     : https://prove2.me/theorems/a6be7f96-2481-443b-959c-af85a1f7afbe
-- title:
--   Cardinality of a multiplicatively close set of maxima
-- statement:
--   Suppose a finite set $S$ of natural numbers has all its members at most $N$, and $80y<87x$ for all $x,y\in S$. Then $87|S|\le7N+87$.
-- source:
--   Erdős Problem 287, https://www.erdosproblems.com/287.

import Mathlib

theorem Erdos287.card_bound_for_close_maximum_cluster (S : Finset ℕ) (N : ℕ) (hN : ∀ x ∈ S, x ≤ N)
    (hclose : ∀ x ∈ S, ∀ y ∈ S, 80 * y < 87 * x) :
    87 * S.card ≤ 7 * N + 87 := by sorry
