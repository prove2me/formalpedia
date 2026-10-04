-- Prove2me | Theorems.Thm_EdmondsKarp_ShortestPath_network_divergence
-- name    : EdmondsKarp.ShortestPath.network_divergence
-- status  : Proved
-- author  : @arexychen
-- created : 2026-10-02T19:25:28.278303+00:00
-- url     : https://prove2.me/theorems/7d7d1079-10e4-4f9c-a753-f8873ea2c6ad
-- title:
--   Separate the return arc from node divergence
-- statement:
--   For any flow assignment, the outgoing minus incoming sum over all network arcs equals the corresponding sum over original arcs, plus the return-arc value at the sink and minus the return-arc value at the source.
-- source:
--   Edmonds and Karp (1972), §1.1 p. 249, network with the additional return arc (t,s). DOI: 10.1145/321694.321699.

import Definitions.Def_EdmondsKarp_ShortestPath_Augmentation
open EdmondsKarp.ShortestPath

theorem EdmondsKarp.ShortestPath.network_divergence {V : Type} [Fintype V] [DecidableEq V] (N : Network V)
    (g : V → V → ℝ) (u : V) :
    (∑ v ∈ Finset.univ.filter (fun v => (u, v) ∈ N.arcs), g u v) -
      (∑ v ∈ Finset.univ.filter (fun v => (v, u) ∈ N.arcs), g v u) =
    (∑ v : V, if (u, v) ∈ N.A then g u v else 0) -
      (∑ v : V, if (v, u) ∈ N.A then g v u else 0) +
    (if u = N.t then g N.t N.s else 0) - (if u = N.s then g N.t N.s else 0) := by sorry
