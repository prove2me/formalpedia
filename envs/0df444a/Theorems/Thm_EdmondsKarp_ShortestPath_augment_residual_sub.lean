-- Prove2me | Theorems.Thm_EdmondsKarp_ShortestPath_augment_residual_sub
-- name    : EdmondsKarp.ShortestPath.augment_residual_sub
-- status  : Proved
-- author  : @arexychen
-- created : 2026-10-02T19:28:10.984412+00:00
-- url     : https://prove2.me/theorems/e9e6a69d-8821-4311-a965-4935bed61da9
-- title:
--   New residual arcs reverse a step of the augmenting path
-- statement:
--   Every residual arc after augmentation either was residual before augmentation or is the reversal of a step on the augmenting path.
-- source:
--   Edmonds and Karp (1972), Theoretical Improvements in Algorithmic Efficiency for Network Flow Problems, §1.1 pp. 249–250 and §1.2 p. 251. DOI: 10.1145/321694.321699.

import Definitions.Def_EdmondsKarp_ShortestPath_Augmentation
open EdmondsKarp.ShortestPath

theorem EdmondsKarp.ShortestPath.augment_residual_sub {V : Type} [Fintype V] [DecidableEq V] (N : Network V)
    (f : V → V → ℝ) (P : List V) (hf : IsFlow N f) (hP : IsAugPath N f P)
    (u v : V) (h : ResArc N (augment N f P) u v) :
    ResArc N f u v ∨ (v, u) ∈ pathArcs P := by sorry
