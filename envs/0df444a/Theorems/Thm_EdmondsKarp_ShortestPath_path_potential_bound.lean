-- Prove2me | Theorems.Thm_EdmondsKarp_ShortestPath_path_potential_bound
-- name    : EdmondsKarp.ShortestPath.path_potential_bound
-- status  : Proved
-- author  : @arexychen
-- created : 2026-10-02T20:07:33.756518+00:00
-- url     : https://prove2.me/theorems/bec4778c-5cc4-4b70-ac70-705555644daf
-- title:
--   A unit edge bound controls potential change along a walk
-- statement:
--   If an extended-natural vertex potential increases by at most one along each directed edge, its increase between the endpoints of a finite directed walk is at most the number of edges in that walk.
-- source:
--   Edmonds and Karp (1972), §1.2 p. 252, proof of residual-distance monotonicity and reversed-arc growth. DOI: 10.1145/321694.321699.

import Definitions.Def_EdmondsKarp_ShortestPath_Run
open EdmondsKarp.ShortestPath

theorem EdmondsKarp.ShortestPath.path_potential_bound {V : Type} [Fintype V] [DecidableEq V] (R : V → V → Prop)
    (d : V → ℕ∞) (hd : ∀ u v, R u v → d v ≤ d u + 1)
    (P : List V) (u v : V) (hh : P.head? = some u) (hl : P.getLast? = some v)
    (hc : P.IsChain R) : d v ≤ d u + ((pathArcs P).length : ℕ∞) := by sorry
