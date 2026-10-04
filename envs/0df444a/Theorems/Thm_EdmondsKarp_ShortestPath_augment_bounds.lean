-- Prove2me | Theorems.Thm_EdmondsKarp_ShortestPath_augment_bounds
-- name    : EdmondsKarp.ShortestPath.augment_bounds
-- status  : Proved
-- author  : @arexychen
-- created : 2026-10-02T19:24:33.111974+00:00
-- url     : https://prove2.me/theorems/087e7832-333b-4837-be4c-bdf930b12dc4
-- title:
--   Augmentation preserves arc bounds and increases the return flow
-- statement:
--   For a feasible flow and an augmenting path, every original arc still has flow between zero and its capacity after augmentation, and the return-arc flow increases by the path bottleneck value.
-- source:
--   Edmonds and Karp (1972), §1.1 p. 249, the augmentation rule in cases (a)–(c). DOI: 10.1145/321694.321699.

import Definitions.Def_EdmondsKarp_ShortestPath_Augmentation
open EdmondsKarp.ShortestPath

theorem EdmondsKarp.ShortestPath.augment_bounds {V : Type} [Fintype V] [DecidableEq V] (N : Network V)
    (f : V → V → ℝ) (P : List V) (hf : IsFlow N f) (hP : IsAugPath N f P) :
    (∀ u v, (u, v) ∈ N.A →
      0 ≤ augment N f P u v ∧ augment N f P u v ≤ N.c u v) ∧
    augment N f P N.t N.s = f N.t N.s + pathEps N f P := by sorry
