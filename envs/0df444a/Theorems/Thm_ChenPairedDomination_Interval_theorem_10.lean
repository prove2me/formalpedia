-- Prove2me | Theorems.Thm_ChenPairedDomination_Interval_theorem_10
-- name    : ChenPairedDomination.Interval.theorem_10
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-10-31T01:27:09.015999+00:00
-- url     : https://prove2.me/theorems/47933156-80b9-4eae-81c7-f3890cf46bbd
-- title:
--   Theorem 10 — MPDI is optimal and runs in linear time
-- statement:
--   There is one positive absolute constant C such that for every finite connected simple interval graph G without isolated vertices, with n vertices, m undirected edges, a supplied left-endpoint order certified by nonempty closed real intervals, and any duplicate-free adjacency-list representation in that order, the concrete algorithm MPDI returns a minimum paired-dominating set S and has counted execution time
--
--   $$\operatorname{cost}(\mathrm{MPDI},G)\le C(n+m).$$
--
--   S dominates G, the induced graph G[S] has a perfect matching, and |S| ≤ |T| for every paired-dominating set T of G. The count includes F preprocessing, zero initialization, the complete reverse loop with every neighborhood visit, and final output collection. C is independent of n, G, the representation, and the order. The intervals are a mathematical certificate; the input order is already supplied and no endpoint sorting is charged.
--
--   Differences from the source:
--   - encoding: vertices u_1,...,u_n and prefixes V_r → vertices Fin n, with u_i at index i-1 and prefixVertices r containing indices below r; reason: this is the same finite ordered enumeration
--   - encoding: an interval representation ordered by increasing left endpoints → nonempty closed real intervals with nondecreasing left endpoints, permitting ties and point intervals; reason: this makes the endpoint convention explicit without restricting lengths or the real endpoint domain
--   - encoding: a minimum paired-dominating set of G → a subset that dominates all vertices, has a perfect matching on its own induced carrier, and is no larger than any feasible competitor; reason: this makes feasibility and minimum cardinality explicit without choosing a distinguished optimizer
--   - encoding: connected simple graphs without isolated vertices → G.Connected and n ≥ 2; reason: for finite connected simple graphs these describe exactly the standing non-isolated domain
--   - encoding: MPDI runs in O(m+n) given the vertex order → one positive natural constant before all inputs bounds a fixed unit-cost RAM operation counter for the concrete run; reason: a natural constant is equivalent to a real big-O constant after rounding; the counter includes preprocessing, all repeated neighbor visits and output, with indexed adjacency lists and mutable-array semantics
-- source:
--   Chen, Lu and Zeng, arXiv:0802.2742v1 (2008), https://arxiv.org/abs/0802.2742v1, Theorem 10, p. 13

import Definitions.Def_ChenPairedDomination_Interval_PrefixData
import Definitions.Def_ChenPairedDomination_Interval_MPDI
open ChenPairedDomination.Interval

namespace ChenPairedDomination.Interval

theorem theorem_10 :
    ∃ C : ℕ, 0 < C ∧
      ∀ (n : ℕ), 2 ≤ n →
      ∀ (G : SimpleGraph (Fin n)) (R : OrderedRepresentation G), G.Connected →
      ∀ A : AdjacencyList n G,
        MinimumPairedDominatesOn G Finset.univ (resultSet n (runMPDI n A.rows)) ∧
        (runMPDI n A.rows).cost ≤ C * (n + edgeCount G) := by sorry

end ChenPairedDomination.Interval
