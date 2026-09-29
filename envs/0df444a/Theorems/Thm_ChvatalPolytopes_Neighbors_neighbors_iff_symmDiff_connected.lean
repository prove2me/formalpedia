-- Prove2me | Theorems.Thm_ChvatalPolytopes_Neighbors_neighbors_iff_symmDiff_connected
-- name    : ChvatalPolytopes.Neighbors.neighbors_iff_symmDiff_connected
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-26T20:22:56.928332+00:00
-- url     : https://prove2.me/theorems/e2a76047-7dd8-42af-8acf-220aa5d07b05
-- title:
--   Theorem 6.2 — stable sets are adjacent on $P(G)$ iff their symmetric difference induces a connected subgraph
-- statement:
--   Let $G=(V,E)$ be a finite graph and $P(G)$ its stable set polytope, the convex hull of the set $S(G)$ of incidence vectors of stable sets. Let $y,z\in S(G)$ and let
--   $$Y=\{u : y_u=1\},\qquad Z=\{u : z_u=1\}$$
--   be the corresponding stable sets. Then $y$ and $z$ are neighbours in $P(G)$ — there is an integer-valued vector $c$ such that $y$ and $z$ are the only two maximizers of $cx$ over $S(G)$ — if and only if
--   $$\text{the subgraph } H \text{ of } G \text{ induced by } (Y-Z)\cup(Z-Y) \text{ is connected.}$$
--
--   The theorem describes the edges (the 1-skeleton) of the stable set polytope purely in terms of the graph. Applied to the line graph it answers Balinski's question on adjacency in the matching polytope (Corollary 6.3).
--
--   **Formalization Note** "Connected" is Mathlib's `SimpleGraph.Connected`, which requires a nonempty vertex set; hence for $y=z$ both sides are false, as in the paper (neighbours are two distinct vectors). Neighbourhood is the paper's definition via unique maximizers of integer-valued objectives (`AreNeighbors`).
-- source:
--   Chvátal, On certain polytopes associated with graphs, J. Combin. Theory Ser. B 18 (1975), p. 149, Theorem 6.2

import Mathlib
import Definitions.Def_ChvatalPolytopes_Neighbors_StablePolytope
import Definitions.Def_ChvatalPolytopes_Neighbors_AreNeighbors

namespace ChvatalPolytopes.Neighbors

/-- **Theorem 6.2** (Chvátal 1975, p. 149). Let `G = (V, E)` be a graph. Let `y, z` be vectors
from `S(G)`; let `Y, Z` be the corresponding stable sets (`Y = {u : y_u = 1}`,
`Z = {u : z_u = 1}`). Then `y` and `z` are neighbors in `P(G)` if and only if the subgraph `H`
of `G` induced by `(Y − Z) ∪ (Z − Y)` is connected. -/
theorem neighbors_iff_symmDiff_connected {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (y z : V → ℝ) (hy : y ∈ stableVectors G) (hz : z ∈ stableVectors G) :
    AreNeighbors G y z ↔
      (G.induce ((onesSet y \ onesSet z) ∪ (onesSet z \ onesSet y))).Connected := by sorry

end ChvatalPolytopes.Neighbors
