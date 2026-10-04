-- Prove2me | Theorems.Thm_EdmondsKarp_ShortestPath_resDist_triangle
-- name    : EdmondsKarp.ShortestPath.resDist_triangle
-- status  : Proved
-- author  : @arexychen
-- created : 2026-10-02T19:52:34.492812+00:00
-- url     : https://prove2.me/theorems/94385889-4121-4fb5-bab3-6d61ee320ed0
-- title:
--   Triangle inequality for residual distance
-- statement:
--   Residual distance satisfies the triangle inequality, with infinite distance allowed for unreachable pairs.
-- source:
--   Edmonds and Karp (1972), §1.2 p. 251, residual shortest-path distance. DOI: 10.1145/321694.321699.

import Definitions.Def_EdmondsKarp_ShortestPath_Run
open EdmondsKarp.ShortestPath

theorem EdmondsKarp.ShortestPath.resDist_triangle {V : Type} [Fintype V] [DecidableEq V] (N : Network V)
    (f : V → V → ℝ) (a b c : V) :
    resDist N f a c ≤ resDist N f a b + resDist N f b c := by sorry
