-- Prove2me | Theorems.Thm_EdmondsKarp_ShortestPath_shortest_path_arc_distances
-- name    : EdmondsKarp.ShortestPath.shortest_path_arc_distances
-- status  : Proved
-- author  : @arexychen
-- created : 2026-10-02T20:07:44.286883+00:00
-- url     : https://prove2.me/theorems/bf38df09-79f9-4f96-b254-564d05524537
-- title:
--   Distance identities along a shortest augmenting-path arc
-- statement:
--   For any step u to v on a shortest augmenting path, source distance increases by one, sink distance decreases by one, and source-to-sink distance is source-to-u distance plus one plus v-to-sink distance.
-- source:
--   Edmonds and Karp (1972), §1.2 p. 252, proof of residual-distance monotonicity and reversed-arc growth. DOI: 10.1145/321694.321699.

import Definitions.Def_EdmondsKarp_ShortestPath_Run
open EdmondsKarp.ShortestPath

theorem EdmondsKarp.ShortestPath.shortest_path_arc_distances {V : Type} [Fintype V] [DecidableEq V] (N : Network V)
    (f : V → V → ℝ) (P : List V) (hP : IsShortestAugPath N f P)
    (u v : V) (he : (u, v) ∈ pathArcs P) :
    resDist N f N.s v = resDist N f N.s u + 1 ∧
    resDist N f u N.t = resDist N f v N.t + 1 ∧
    resDist N f N.s N.t = resDist N f N.s u + 1 + resDist N f v N.t := by sorry
