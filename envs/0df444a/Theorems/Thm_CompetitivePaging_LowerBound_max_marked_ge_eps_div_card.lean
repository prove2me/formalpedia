-- Prove2me | Theorems.Thm_CompetitivePaging_LowerBound_max_marked_ge_eps_div_card
-- name    : CompetitivePaging.LowerBound.max_marked_ge_eps_div_card
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-27T13:19:43.73737+00:00
-- url     : https://prove2.me/theorems/cf8ed404-858e-4a69-877b-60e76ab63f84
-- title:
--   While $P > \epsilon$, the most probable marked vertex has $p_i \ge \epsilon/|S| > 0$
-- statement:
--   Let $M$ be a finite set of vertices and $p=(p_i)_{i\in M}$ a probability vector ($p_i\ge0$, $\sum_i p_i=1$). Let $S\subseteq M$ be the set of marked vertices, $P=\sum_{j\in S}p_j$, and let $\epsilon>0$. Suppose $P>\epsilon$ and let $i\in S$ be a marked vertex of maximal probability, $p_i=\max_{j\in S}p_j$. Then
--
--   $$
--   p_i\ \ge\ \frac{\epsilon}{|S|}\ >\ 0 .
--   $$
--
--   In the lower-bound construction, the loop of a subphase requests the most probable marked vertex while $P>\epsilon$; each such request costs the on-line algorithm $p_i$ in expectation, so each iteration adds at least $\epsilon/|S|>0$ to the expected cost of the subphase, which is why the loop terminates.
-- source:
--   Fiat, Karp, Luby, McGeoch, Sleator, Young, Competitive Paging Algorithms, arXiv:cs/0205038v1, p. 7, §5, proof of Theorem 4 ("Each iteration of this loop adds at least ε/|S| > 0 to the total expected cost of this subphase.")

import Mathlib

namespace CompetitivePaging.LowerBound

theorem max_marked_ge_eps_div_card {M : Type} [Fintype M] (p : M → ℝ)
    (hp : ∀ i, 0 ≤ p i) (hsum : ∑ i, p i = 1) (S : Finset M) (ε : ℝ) (hε : 0 < ε)
    (hP : ε < ∑ j ∈ S, p j) (i : M) (hi : i ∈ S) (hmax : ∀ j ∈ S, p j ≤ p i) :
    ε / S.card ≤ p i ∧ 0 < ε / S.card := by sorry

end CompetitivePaging.LowerBound
