-- Prove2me | Theorems.Thm_CompOT_Vertices_prop_3_4_forest_edge_bound
-- name    : CompOT.Vertices.prop_3_4_forest_edge_bound
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T01:23:30.895244+00:00
-- url     : https://prove2.me/theorems/da2f0eb1-8777-4ef9-aaa7-1aef1989884b
-- title:
--   Proof of Proposition 3.4, p. 407 — a graph with k nodes and no cycles has at most k − 1 edges
-- statement:
--   Let $G$ be a simple graph on a finite set of $k$ vertices. If $G$ has no cycles (it is a forest), then
--   $$|E(G)| \le k - 1 .$$
--
--   This is the counting step that turns the acyclicity of the support graph into the bound of $n + m - 1$ nonzero entries.
--
--   **Formalization Note** $k - 1$ is natural-number subtraction; for $k = 0$ it reads $0$, which is correct since the empty graph has no edges. The number of edges is `Nat.card G.edgeSet`.
-- source:
--   Peyré & Cuturi, Computational Optimal Transport (FnT ML 2019), §3.4.1, end of the proof of Proposition 3.4, p. 407

import Mathlib

namespace CompOT.Vertices

/-- End of the proof of Proposition 3.4, p. 407: a graph with `k` nodes and no cycles has at
most `k − 1` edges. Stated for a simple graph on a finite vertex type; `k − 1` is natural
subtraction, which for `k = 0` reads `0` (the empty graph has no edges). -/
theorem prop_3_4_forest_edge_bound {V : Type*} [Finite V] (G : SimpleGraph V)
    (hG : G.IsAcyclic) :
    Nat.card G.edgeSet ≤ Nat.card V - 1 := by sorry

end CompOT.Vertices
