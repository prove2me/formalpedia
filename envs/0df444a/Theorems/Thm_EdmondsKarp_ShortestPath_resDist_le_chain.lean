-- Prove2me | Theorems.Thm_EdmondsKarp_ShortestPath_resDist_le_chain
-- name    : EdmondsKarp.ShortestPath.resDist_le_chain
-- status  : Proved
-- author  : @arexychen
-- created : 2026-10-02T19:39:37.827857+00:00
-- url     : https://prove2.me/theorems/224e72a8-c5f4-40f8-a64b-99da4ee705ea
-- title:
--   Residual distance is bounded by any residual walk
-- statement:
--   The residual distance between the endpoints of a finite nonempty residual chain is at most its number of consecutive arcs, even if the chain repeats vertices.
-- source:
--   Edmonds and Karp (1972), §1.2 p. 251, residual distance; auxiliary loop-removal argument. DOI: 10.1145/321694.321699.

import Definitions.Def_EdmondsKarp_ShortestPath_Run
open EdmondsKarp.ShortestPath

theorem EdmondsKarp.ShortestPath.resDist_le_chain {V : Type} [Fintype V] [DecidableEq V] (N : Network V)
    (f : V → V → ℝ) (u v : V) (P : List V)
    (hh : P.head? = some u) (hl : P.getLast? = some v) (hc : P.IsChain (ResArc N f)) :
    resDist N f u v ≤ ((pathArcs P).length : ℕ∞) := by sorry
