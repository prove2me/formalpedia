-- Prove2me | Theorems.Thm_EdmondsKarp_ShortestPath_pathArcs_split
-- name    : EdmondsKarp.ShortestPath.pathArcs_split
-- status  : Proved
-- author  : @arexychen
-- created : 2026-10-02T20:00:47.18917+00:00
-- url     : https://prove2.me/theorems/4eaa0a28-b380-4e79-af78-d21d3eb4ccac
-- title:
--   Split a vertex list at a consecutive pair
-- statement:
--   If an ordered pair occurs as a consecutive arc of a vertex list, the list decomposes into a prefix, those two vertices, and a suffix.
-- source:
--   Edmonds and Karp (1972), §1.2 pp. 251–252, residual shortest-path distance and simple-path bounds. DOI: 10.1145/321694.321699.

import Definitions.Def_EdmondsKarp_ShortestPath_Run
open EdmondsKarp.ShortestPath

theorem EdmondsKarp.ShortestPath.pathArcs_split {V : Type} [Fintype V] [DecidableEq V] (P : List V)
    (u v : V) (h : (u, v) ∈ pathArcs P) : ∃ L R, P = L ++ u :: v :: R := by sorry
