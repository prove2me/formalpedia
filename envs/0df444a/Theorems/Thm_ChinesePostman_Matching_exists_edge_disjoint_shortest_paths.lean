-- Prove2me | Theorems.Thm_ChinesePostman_Matching_exists_edge_disjoint_shortest_paths
-- name    : ChinesePostman.Matching.exists_edge_disjoint_shortest_paths
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T06:51:59.841907+00:00
-- url     : https://prove2.me/theorems/337733e9-2f6e-4eeb-8cd7-69341187c003
-- title:
--   §3, p. 92 — uncross the matched shortest paths
-- statement:
--   Let $G$ be a connected finite loopless multigraph with nonnegative edge lengths $c_e$. Let $d(u,v)$ be an attained shortest-path distance for every pair of nodes, and let $M$ be a 1-matching of the odd-degree nodes. There is another 1-matching $M'$ with no larger length and a shortest path for each matched pair such that paths belonging to different pairs share no original edge:
--
--   $$
--   L(M')\le L(M),\qquad
--   \ell(P_{uv})=\sum_{e\in P_{uv}}c_e=d(u,v)\quad\text{for every pair }\{u,v\}\in M',
--   $$
--
--   where $L(M)=\sum_{\{u,v\}\in M}d(u,v)$ and $P_{uv}$ is the edge-simple path chosen for the pair $\{u,v\}$. The edge-disjoint paths permit a zero-or-one assignment of additional traversals.
--
--
--
--   **Formalization Note** Each path is indexed by both endpoints; the second orientation is the reverse of the first, and edge disjointness applies only to distinct matched pairs.
-- source:
--   Edmonds and Johnson, Matching, Euler tours and the Chinese postman, Math. Programming 5 (1973), p. 92, §3, uncrossing paragraph, https://doi.org/10.1007/BF01580113

import Mathlib
import Definitions.Def_ChinesePostman_Matching_Setting

namespace ChinesePostman.Matching


/-- §3, p. 92: overlapping shortest paths of matching edges can be uncrossed. -/
theorem exists_edge_disjoint_shortest_paths
    {V E : Type*} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]
    (G : EdmondsMatching65.Polyhedron.Graph V E) (hG : Connected G) (c : E → ℝ) (hc : ∀ e, 0 ≤ c e)
    (d : V → V → ℝ) (hd : ∀ i j, IsShortestPathLength G c i j (d i j))
    (f : V → V) (hf : IsOddPerfectMatching G f) :
    ∃ f' : V → V, IsOddPerfectMatching G f' ∧
      matchingLength G d f' ≤ matchingLength G d f ∧
      ∃ P : V → List V × List E, MatchingPaths G f' P ∧
        ∀ v ∈ oddNodes G, walkLength c (P v).2 = d v (f' v) := by sorry
end ChinesePostman.Matching
