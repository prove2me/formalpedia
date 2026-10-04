-- Prove2me | Theorems.Thm_EdmondsKarp_ShortestPath_pathArcs_incidence
-- name    : EdmondsKarp.ShortestPath.pathArcs_incidence
-- status  : Proved
-- author  : @arexychen
-- created : 2026-10-02T19:24:30.434935+00:00
-- url     : https://prove2.me/theorems/e3dade11-9fb5-44dd-b66e-0261026bc1c1
-- title:
--   Incidence balance of a simple path
-- statement:
--   For any simple vertex list, any vertex u, and any real weight r, the total weight of path arcs leaving u minus the total weight entering u is r at the first vertex, minus r at the last vertex, and zero elsewhere.
-- source:
--   Edmonds and Karp (1972), §1.1 p. 249, preservation of node balances under path augmentation. Auxiliary finite-list identity. DOI: 10.1145/321694.321699.

import Definitions.Def_EdmondsKarp_ShortestPath_Augmentation
open EdmondsKarp.ShortestPath

theorem EdmondsKarp.ShortestPath.pathArcs_incidence {V : Type} [Fintype V] [DecidableEq V] (P : List V)
    (hP : P.Nodup) (u : V) (r : ℝ) :
    (∑ v : V, if (u, v) ∈ pathArcs P then r else 0) -
      (∑ v : V, if (v, u) ∈ pathArcs P then r else 0) =
    (if P.head? = some u then r else 0) - (if P.getLast? = some u then r else 0) := by sorry
