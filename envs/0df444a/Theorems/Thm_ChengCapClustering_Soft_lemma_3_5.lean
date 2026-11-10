-- Prove2me | Theorems.Thm_ChengCapClustering_Soft_lemma_3_5
-- name    : ChengCapClustering.Soft.lemma_3_5
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T01:52:21.249797+00:00
-- url     : https://prove2.me/theorems/94891892-4b6c-42fb-890d-0bbff12e4900
-- title:
--   Lemma 3.5 — transport forest: an integral plan with forest support and $T\le(A^{1/z}+\mathrm{cost}(S^*)^{1/z})^z\le2^{z-1}(A+\mathrm{cost}(S^*))$
-- statement:
--   Let $B$ be a block partition (blocks $I$, sizes $w_i$, representatives $a_i$, total internal cost $A$) and $S^*$ a soft solution with at most $k$ centers at locations in $F$ (center $j$ at $c_j$ serving $\ell_j\le U$ clients), $z\ge1$. There is an integral transport plan $\pi$ with row sums $w_i$ and column sums $\ell_j$ whose support is a forest and whose cost $T=\sum_{i,j}\pi_{ij}\mathrm{dist}(a_i,c_j)^z$ satisfies $T\le(A^{1/z}+\mathrm{cost}(S^*)^{1/z})^z\le 2^{z-1}(A+\mathrm{cost}(S^*))$.
--
--   Differences from the source:
--   - encoding: J = the centers of S* that serve clients → all centers of S* (Fin numCenters), column sums = loads; reason: a center with load 0 has an all-zero column and is an isolated vertex of the support, so the plans and the forest condition are the same
--   - encoding: the support is a forest → `(supportGraph π).IsAcyclic` on the vertex type I ⊕ J; reason: disjoint union of the index sets
--   - generalization: Section 3 works with finite F and jointly bounded doubling dimension → any location set F in any metric space; reason: the finite client and center families suffice for transport and Minkowski; the source instances are included without changing either cost bound
-- source:
--   Cheng, Mo, Ding 2026, Constant-Factor Approximation for Capacitated Clustering in Low Dimension with (1+ε)k Centers, arXiv:2610.40625 (held manuscript SHA-256 9d298191e7086ee0bbea53e5a3e4e9b0fe88c438ed58257f01f3c524a8ac4edb; arXiv version suffix unresolved, citation hold), Lemma 3.5, printed p. 8 / PDF p. 10

import Mathlib
import Definitions.Def_ChengCapClustering_Soft_Clustering

universe u

namespace ChengCapClustering.Soft

/-- Lemma 3.5 (Transport forest), printed p. 8 / PDF p. 10. For a block partition and a soft
solution `S*` with at most `k` centers, some integral transport plan `π` with row sums `w_i` and
column sums `ℓ_j` (the loads of the centers of `S*`) has a forest as support and cost
`T = ∑ π_ij dist(a_i, c_j)^z ≤ (A^{1/z} + cost(S*)^{1/z})^z ≤ 2^{z−1}(A + cost(S*))`. -/
theorem lemma_3_5 (V : Type u) [MetricSpace V] (z : ℝ) (hz : 1 ≤ z) (n k U : ℕ)
    (p : Fin n → V) (F : Set V) (hk : 0 < k) (hkn : k < n) (hU : 0 < U) (hnU : n ≤ k * U)
    (B : BlockPartition V n) (hB : IsBlockPartition k U F B)
    (Sstar : SoftSolution V n) (hS : IsSoftSolution F U k Sstar) :
    ∃ π : Fin B.numBlocks → Fin Sstar.numCenters → ℕ,
      (∀ i, ∑ j, π i j = B.size i) ∧ (∀ j, ∑ i, π i j = Sstar.load j) ∧
      (supportGraph π).IsAcyclic ∧
      (∑ i, ∑ j, (π i j : ℝ) * dist (B.rep i) (Sstar.loc j) ^ z ≤
        (B.totalCost z p ^ (1 / z) + Sstar.cost z p ^ (1 / z)) ^ z) ∧
      (B.totalCost z p ^ (1 / z) + Sstar.cost z p ^ (1 / z)) ^ z ≤
        (2 : ℝ) ^ (z - 1) * (B.totalCost z p + Sstar.cost z p) := by sorry

end ChengCapClustering.Soft
