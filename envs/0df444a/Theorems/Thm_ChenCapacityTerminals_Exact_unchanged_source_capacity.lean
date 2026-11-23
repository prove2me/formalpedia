-- Prove2me | Theorems.Thm_ChenCapacityTerminals_Exact_unchanged_source_capacity
-- name    : ChenCapacityTerminals.Exact.unchanged_source_capacity
-- status  : Open
-- author  : @Mr Robbins
-- created : 2026-11-23T02:28:43.054711+00:00
-- url     : https://prove2.me/theorems/e8cd190c-ce7c-4c44-8a18-c6923b02898c
-- title:
--   Capacity entering an unchanged source from the greedy cover
-- statement:
--   Let $G$ be a prepared rooted network, let $1\le d\le |V(G)|$, and suppose every nonempty root-avoiding entering cut has capacity at least $L>0$. In a legal construction, let $D$ be the greedy common-predecessor set and let $A$ be an unchanged final source excluding $r$. Then
--
--   $$
--   w(D\setminus A,A)\ge \frac{3L}{4d}.
--   $$
--
--   Writing $\tau=L/(4d)$, every external tail of $A$ has capacity at most $\tau$ into $A$. In the sorted tail list, a greedy vertex hitting one full group has capacity at least $1/d$ times the total capacity of the following group, including a partial final group. Disjointness of consecutive groups gives $d\,w(D\setminus A,A)\ge f(A)-d\tau\ge L-d\tau=3L/4$. The statement also covers real-valued capacities and arbitrary legal ties.
-- source:
--   Thomas Chen, STOC 2027 submission #665 (October 2026), PDF p. 5 (printed p. 4), Lemma 2.2, capacity assertion and second paragraph of its proof; https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/665.pdf#page=5

import Definitions.Def_ChenCapacityTerminals_Exact_Construction

set_option autoImplicit false

theorem ChenCapacityTerminals.Exact.unchanged_source_capacity (G : Network) (r d : ℕ) (L : ℚ) (b : ℕ → ℕ) (t : ℕ)
    (c : Construction) (hprep : Prepared G r) (hd : 1 ≤ d)
    (hdn : d ≤ G.vertices.card) (hL : 0 < L)
    (hc : LegalConstruction G r d L b t c) :
    RootLowerBound G r L → ∀ A ∈ unchangedSources G r ((L : ℝ) / (4 * d))
      (c.partitions (c.rounds - 1)),
    3 * (L : ℝ) / (4 * d) ≤ weight G (c.greedy.toFinset \ A) A := by sorry
