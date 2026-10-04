-- Prove2me | Theorems.Thm_EdmondsKarp_ShortestPath_augment_bottleneck
-- name    : EdmondsKarp.ShortestPath.augment_bottleneck
-- status  : Proved
-- author  : @arexychen
-- created : 2026-10-02T19:27:44.797515+00:00
-- url     : https://prove2.me/theorems/ed86ac91-4d5b-4f14-b2a8-3494533a231c
-- title:
--   A bottleneck arc disappears after augmentation
-- statement:
--   For a feasible flow and an augmenting path, any bottleneck step is absent from the residual network after augmentation.
-- source:
--   Edmonds and Karp (1972), Theoretical Improvements in Algorithmic Efficiency for Network Flow Problems, §1.1 pp. 249–250 and §1.2 p. 251. DOI: 10.1145/321694.321699.

import Definitions.Def_EdmondsKarp_ShortestPath_Augmentation
open EdmondsKarp.ShortestPath

theorem EdmondsKarp.ShortestPath.augment_bottleneck {V : Type} [Fintype V] [DecidableEq V] (N : Network V)
    (f : V → V → ℝ) (P : List V) (hf : IsFlow N f) (hP : IsAugPath N f P)
    (u v : V) (hb : IsBottleneck N f P u v) :
    ¬ ResArc N (augment N f P) u v := by sorry
