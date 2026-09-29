-- Prove2me | Theorems.Thm_CompetitivePaging_LowerBound_subphase_final_bound
-- name    : CompetitivePaging.LowerBound.subphase_final_bound
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-27T13:20:21.568309+00:00
-- url     : https://prove2.me/theorems/e133b7ab-a357-46ee-b302-1da59f7f96d8
-- title:
--   $\epsilon + p_j \ge \epsilon + (1-P)/u \ge \epsilon + (1-\epsilon)/u \ge 1/u$
-- statement:
--   Let $M$ be a finite set of $n$ vertices and $p=(p_i)_{i\in M}$ a probability vector ($p_i\ge0$, $\sum_i p_i=1$). Let $S\subsetneq M$ be the set of marked vertices, $P=\sum_{i\in S}p_i$, and $u=n-|S|\ge 1$. Let $\epsilon\ge0$ with $P\le\epsilon$, and let $j\notin S$ be an unmarked vertex of highest probability. Then
--
--   $$
--   \epsilon+p_j\ \ge\ \epsilon+\frac{1-P}{u}\ \ge\ \epsilon+\frac{1-\epsilon}{u}\ \ge\ \frac1u .
--   $$
--
--   In the lower-bound construction, $\epsilon$ is the expected cost of the first request of a subphase and $p_j$ that of its last request, so this chain shows that a subphase whose loop ends with $P\le\epsilon$ costs the on-line algorithm at least $1/u$ in expectation.
-- source:
--   Fiat, Karp, Luby, McGeoch, Sleator, Young, Competitive Paging Algorithms, arXiv:cs/0205038v1, p. 8, §5, proof of Theorem 4 (displayed inequality "expected cost of the subphase ≥ ε + p_j ≥ ε + (1 − P)/u ≥ ε + (1 − ε)/u ≥ 1/u")

import Mathlib

namespace CompetitivePaging.LowerBound

theorem subphase_final_bound {M : Type} [Fintype M] (p : M → ℝ)
    (hp : ∀ i, 0 ≤ p i) (hsum : ∑ i, p i = 1) (S : Finset M)
    (hS : S.card < Fintype.card M) (ε : ℝ) (hε : 0 ≤ ε) (hPε : ∑ i ∈ S, p i ≤ ε)
    (j : M) (hj : j ∉ S) (hmax : ∀ j' ∉ S, p j' ≤ p j) :
    ε + p j ≥ ε + (1 - ∑ i ∈ S, p i) / ((Fintype.card M : ℝ) - S.card) ∧
    ε + (1 - ∑ i ∈ S, p i) / ((Fintype.card M : ℝ) - S.card) ≥
      ε + (1 - ε) / ((Fintype.card M : ℝ) - S.card) ∧
    ε + (1 - ε) / ((Fintype.card M : ℝ) - S.card) ≥
      1 / ((Fintype.card M : ℝ) - S.card) := by sorry

end CompetitivePaging.LowerBound
