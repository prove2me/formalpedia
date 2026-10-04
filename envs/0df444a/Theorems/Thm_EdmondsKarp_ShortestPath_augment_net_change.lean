-- Prove2me | Theorems.Thm_EdmondsKarp_ShortestPath_augment_net_change
-- name    : EdmondsKarp.ShortestPath.augment_net_change
-- status  : Proved
-- author  : @arexychen
-- created : 2026-10-02T19:24:57.008022+00:00
-- url     : https://prove2.me/theorems/fea0f5cd-afe2-48b7-b359-53de8e93e7d8
-- title:
--   Net flow change on each pair of opposite arcs
-- statement:
--   For an augmenting path, the change in forward original-arc flow minus the change in reverse original-arc flow equals the bottleneck amount times the signed path incidence on that vertex pair. Missing original arcs contribute zero.
-- source:
--   Edmonds and Karp (1972), §1.1 p. 249, the augmentation rule in cases (a)–(c). DOI: 10.1145/321694.321699.

import Definitions.Def_EdmondsKarp_ShortestPath_Augmentation
open EdmondsKarp.ShortestPath

theorem EdmondsKarp.ShortestPath.augment_net_change {V : Type} [Fintype V] [DecidableEq V] (N : Network V)
    (f : V → V → ℝ) (P : List V) (hP : IsAugPath N f P) (u v : V) :
    (if (u, v) ∈ N.A then augment N f P u v - f u v else 0) -
      (if (v, u) ∈ N.A then augment N f P v u - f v u else 0) =
    (if (u, v) ∈ pathArcs P then pathEps N f P else 0) -
      (if (v, u) ∈ pathArcs P then pathEps N f P else 0) := by sorry
