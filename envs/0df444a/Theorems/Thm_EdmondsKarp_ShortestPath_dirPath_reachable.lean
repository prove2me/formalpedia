-- Prove2me | Theorems.Thm_EdmondsKarp_ShortestPath_dirPath_reachable
-- name    : EdmondsKarp.ShortestPath.dirPath_reachable
-- status  : Proved
-- author  : @arexychen
-- created : 2026-10-02T19:35:45.284955+00:00
-- url     : https://prove2.me/theorems/fe64df2b-4fad-41d5-865a-6402be79f441
-- title:
--   Residual reachability is equivalent to a simple directed path
-- statement:
--   Two vertices are related by the reflexive transitive closure of residual adjacency if and only if there is a simple directed residual path between them.
-- source:
--   Auxiliary lemmas for the augmenting-path optimality criterion in Edmonds and Karp (1972), §1.1 p. 249. DOI: 10.1145/321694.321699.

import Definitions.Def_EdmondsKarp_ShortestPath_Augmentation
open EdmondsKarp.ShortestPath

theorem EdmondsKarp.ShortestPath.dirPath_reachable {V : Type} [Fintype V] [DecidableEq V] (N : Network V)
    (f : V → V → ℝ) (u v : V) :
    (∃ P, IsDirPath N f u v P) ↔ Relation.ReflTransGen (ResArc N f) u v := by sorry
