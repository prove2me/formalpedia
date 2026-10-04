-- Prove2me | Theorems.Thm_EdmondsKarp_ShortestPath_shortest_path_split
-- name    : EdmondsKarp.ShortestPath.shortest_path_split
-- status  : Proved
-- author  : @arexychen
-- created : 2026-10-02T20:05:26.455107+00:00
-- url     : https://prove2.me/theorems/9ea1293f-2938-4f97-87c5-1fce65065398
-- title:
--   Prefixes and suffixes of a shortest augmenting path realize distance
-- statement:
--   If a shortest augmenting path splits as a prefix L followed by u and a suffix R, the residual distance from the source to u equals the length of L, and the distance from u to the sink equals the length of R.
-- source:
--   Edmonds and Karp (1972), §1.2 pp. 251–252, subpaths of shortest augmenting paths. DOI: 10.1145/321694.321699.

import Definitions.Def_EdmondsKarp_ShortestPath_Run
open EdmondsKarp.ShortestPath

theorem EdmondsKarp.ShortestPath.shortest_path_split {V : Type} [Fintype V] [DecidableEq V] (N : Network V)
    (f : V → V → ℝ) (P : List V) (hP : IsShortestAugPath N f P)
    (L R : List V) (u : V) (he : P = L ++ u :: R) :
    resDist N f N.s u = (L.length : ℕ∞) ∧ resDist N f u N.t = (R.length : ℕ∞) := by sorry
