-- Prove2me | Theorems.Thm_EdmondsKarp_ShortestPath_resDist_basics
-- name    : EdmondsKarp.ShortestPath.resDist_basics
-- status  : Proved
-- author  : @arexychen
-- created : 2026-10-02T20:00:31.250057+00:00
-- url     : https://prove2.me/theorems/25e51c31-8161-49ce-9c7e-840d5af1c1fc
-- title:
--   Residual distance at a vertex and along an arc
-- statement:
--   Residual distance from a vertex to itself is zero, and residual distance along a residual arc is at most one.
-- source:
--   Edmonds and Karp (1972), §1.2 pp. 251–252, residual shortest-path distance and simple-path bounds. DOI: 10.1145/321694.321699.

import Definitions.Def_EdmondsKarp_ShortestPath_Run
open EdmondsKarp.ShortestPath

theorem EdmondsKarp.ShortestPath.resDist_basics {V : Type} [Fintype V] [DecidableEq V] (N : Network V)
    (f : V → V → ℝ) :
    (∀ u : V, resDist N f u u = 0) ∧
    (∀ u v : V, ResArc N f u v → resDist N f u v ≤ 1) := by sorry
