-- Prove2me | Theorems.Thm_ChenPairedDomination_Interval_observation_5
-- name    : ChenPairedDomination.Interval.observation_5
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-10-31T01:27:05.945054+00:00
-- url     : https://prove2.me/theorems/57023bfd-d936-4734-a09f-16ad5e6beeeb
-- title:
--   Observation 5 — left-endpoint adjacency
-- statement:
--   Let G be a finite simple interval graph with vertices u_1,...,u_n ordered by nondecreasing left endpoints of a supplied closed real interval representation. If j < i and u_i is adjacent to u_j, then
--
--   $$u_j u_k \in E(G) \quad\text{for every } j+1\le k\le i.$$
--
--   Connectedness is not required. This is the adjacency property used for ordered prefixes.
--
--   Differences from the source:
--   - encoding: vertices u_1,...,u_n and prefixes V_r → vertices Fin n, with u_i at index i-1 and prefixVertices r containing indices below r; reason: this is the same finite ordered enumeration
--   - encoding: an interval representation ordered by increasing left endpoints → nonempty closed real intervals with nondecreasing left endpoints, permitting ties and point intervals; reason: this makes the endpoint convention explicit without restricting lengths or the real endpoint domain
--   - generalization: the paper’s standing interval-graph domain is connected and excludes isolated vertices → arbitrary interval graphs, including disconnected graphs and isolated vertices; reason: the adjacency implication uses only the ordered endpoints of the displayed vertices and covers every source instance
-- source:
--   Chen, Lu and Zeng, arXiv:0802.2742v1 (2008), https://arxiv.org/abs/0802.2742v1, Observation 5, p. 11

import Definitions.Def_ChenPairedDomination_Interval_PrefixData

namespace ChenPairedDomination.Interval

theorem observation_5
    {n : ℕ} (G : SimpleGraph (Fin n))
    (R : ChenPairedDomination.Interval.OrderedRepresentation G)
    (i j : Fin n) (hji : j < i) (hij : G.Adj i j) :
    ∀ k : Fin n, j < k → k ≤ i → G.Adj j k := by sorry

end ChenPairedDomination.Interval
