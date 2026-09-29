-- Prove2me | Theorems.Thm_CompetitivePaging_LowerBound_max_unmarked_ge_avg
-- name    : CompetitivePaging.LowerBound.max_unmarked_ge_avg
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-27T13:20:01.244376+00:00
-- url     : https://prove2.me/theorems/deb4474c-3648-452d-a50c-d1bfd256e6b3
-- title:
--   The most probable unmarked vertex has $p_j \ge (1-P)/u$
-- statement:
--   Let $M$ be a finite set of $n$ vertices and $p=(p_i)_{i\in M}$ a probability vector ($p_i\ge0$, $\sum_i p_i=1$). Let $S\subsetneq M$ be the set of marked vertices, $P=\sum_{i\in S}p_i$, and $u=n-|S|\ge1$ the number of unmarked vertices. If $j\notin S$ is an unmarked vertex with the highest probability value, $p_j=\max_{j'\notin S}p_{j'}$, then
--
--   $$
--   p_j\ \ge\ \frac{1-P}{u}.
--   $$
--
--   This bounds the expected cost of the request that closes a subphase in the lower-bound construction.
-- source:
--   Fiat, Karp, Luby, McGeoch, Sleator, Young, Competitive Paging Algorithms, arXiv:cs/0205038v1, p. 8, §5, proof of Theorem 4 ("Note that p_j ≥ (1 − P)/u.")

import Mathlib

namespace CompetitivePaging.LowerBound

theorem max_unmarked_ge_avg {M : Type} [Fintype M] (p : M → ℝ)
    (hp : ∀ i, 0 ≤ p i) (hsum : ∑ i, p i = 1) (S : Finset M)
    (hS : S.card < Fintype.card M) (j : M) (hj : j ∉ S) (hmax : ∀ j' ∉ S, p j' ≤ p j) :
    (1 - ∑ i ∈ S, p i) / ((Fintype.card M : ℝ) - S.card) ≤ p j := by sorry

end CompetitivePaging.LowerBound
