-- Prove2me | Theorems.Thm_CompetitivePaging_LowerBound_exists_unmarked_ge_inv_of_marked_zero
-- name    : CompetitivePaging.LowerBound.exists_unmarked_ge_inv_of_marked_zero
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-27T13:19:20.226091+00:00
-- url     : https://prove2.me/theorems/9ad9b1d2-0503-4388-9bec-3c7a51699b1e
-- title:
--   If the marked vertices carry no probability, some unmarked vertex has $p_i \ge 1/u$
-- statement:
--   Let $M$ be a finite set of $n$ vertices and $p=(p_i)_{i\in M}$ a probability vector: $p_i\ge 0$ and $\sum_{i\in M}p_i=1$. Let $S\subsetneq M$ be a set of marked vertices, and let $u=n-|S|\ge 1$ be the number of unmarked vertices. If
--
--   $$
--   P=\sum_{i\in S}p_i=0,
--   $$
--
--   then there is an unmarked vertex $i\notin S$ with
--
--   $$
--   p_i\ \ge\ \frac1u .
--   $$
--
--   In the lower-bound construction this is the case of a subphase consisting of a single request: requesting such a vertex costs the on-line algorithm at least $1/u$ in expectation.
-- source:
--   Fiat, Karp, Luby, McGeoch, Sleator, Young, Competitive Paging Algorithms, arXiv:cs/0205038v1, p. 7, §5, proof of Theorem 4 ("If P = 0 then there must be an unmarked vertex i with p_i ≥ 1/u.")

import Mathlib

namespace CompetitivePaging.LowerBound

theorem exists_unmarked_ge_inv_of_marked_zero {M : Type} [Fintype M] (p : M → ℝ)
    (hp : ∀ i, 0 ≤ p i) (hsum : ∑ i, p i = 1) (S : Finset M)
    (hS : S.card < Fintype.card M) (hP : ∑ i ∈ S, p i = 0) :
    ∃ i ∉ S, 1 / ((Fintype.card M : ℝ) - S.card) ≤ p i := by sorry

end CompetitivePaging.LowerBound
