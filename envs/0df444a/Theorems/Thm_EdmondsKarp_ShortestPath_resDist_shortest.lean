-- Prove2me | Theorems.Thm_EdmondsKarp_ShortestPath_resDist_shortest
-- name    : EdmondsKarp.ShortestPath.resDist_shortest
-- status  : Proved
-- author  : @arexychen
-- created : 2026-10-02T20:01:04.06563+00:00
-- url     : https://prove2.me/theorems/716e678f-8f7b-4659-b9ed-d05a7541e906
-- title:
--   A shortest augmenting path realizes residual distance
-- statement:
--   A shortest augmenting path realizes the residual source-to-sink distance, has at least one arc, and has strictly fewer arcs than the number of vertices.
-- source:
--   Edmonds and Karp (1972), §1.2 pp. 251–252, residual shortest-path distance and simple-path bounds. DOI: 10.1145/321694.321699.

import Definitions.Def_EdmondsKarp_ShortestPath_Run
open EdmondsKarp.ShortestPath

theorem EdmondsKarp.ShortestPath.resDist_shortest {V : Type} [Fintype V] [DecidableEq V] (N : Network V)
    (f : V → V → ℝ) (P : List V) (hP : IsShortestAugPath N f P) :
    resDist N f N.s N.t = ((pathArcs P).length : ℕ∞) ∧
    1 ≤ (pathArcs P).length ∧ (pathArcs P).length < Fintype.card V := by sorry
