-- Prove2me | Theorems.Thm_EdmondsKarp_ShortestPath_pathArcs_simple
-- name    : EdmondsKarp.ShortestPath.pathArcs_simple
-- status  : Proved
-- author  : @arexychen
-- created : 2026-10-02T19:20:16.591986+00:00
-- url     : https://prove2.me/theorems/0aac665c-b371-4423-a245-1cc11f4d8a7a
-- title:
--   Simple paths exclude reversed arcs and endpoint re-entry
-- statement:
--   Let $P$ be a finite list of pairwise distinct vertices. If $(u,v)$ is a consecutive pair of $P$, then $u\ne v$, the reversed pair $(v,u)$ does not occur in $P$, $v$ is not the first vertex, and $u$ is not the last vertex.
-- source:
--   Auxiliary lemma for the simple-path convention in Edmonds and Karp (1972), Theoretical Improvements in Algorithmic Efficiency for Network Flow Problems, J. ACM 19(2), pp. 248–264, §1.1 p. 249. DOI: 10.1145/321694.321699.

import Definitions.Def_EdmondsKarp_ShortestPath_Augmentation

open EdmondsKarp.ShortestPath

theorem EdmondsKarp.ShortestPath.pathArcs_simple {V : Type} [Fintype V] [DecidableEq V] (P : List V)
    (hP : P.Nodup) (u v : V) (h : (u, v) ∈ pathArcs P) :
    u ≠ v ∧ (v, u) ∉ pathArcs P ∧ P.head? ≠ some v ∧ P.getLast? ≠ some u := by sorry
