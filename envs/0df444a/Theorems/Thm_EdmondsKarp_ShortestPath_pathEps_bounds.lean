-- Prove2me | Theorems.Thm_EdmondsKarp_ShortestPath_pathEps_bounds
-- name    : EdmondsKarp.ShortestPath.pathEps_bounds
-- status  : Proved
-- author  : @arexychen
-- created : 2026-10-02T19:21:59.460644+00:00
-- url     : https://prove2.me/theorems/cfc3ef0f-bded-42f9-93ab-3cc6714d19e2
-- title:
--   An augmenting path has a positive bottleneck value
-- statement:
--   For a feasible flow $f$ and an augmenting path $P$, its augmentation amount $\varepsilon(P)$ is positive, is at most the residual amount of every step of $P$, and is attained by a bottleneck arc of $P$.
-- source:
--   Edmonds and Karp (1972), Theoretical Improvements in Algorithmic Efficiency for Network Flow Problems, J. ACM 19(2), §1.1 p. 249, definition of the quantities epsilon_i and their minimum. DOI: 10.1145/321694.321699.

import Definitions.Def_EdmondsKarp_ShortestPath_Augmentation

open EdmondsKarp.ShortestPath

theorem EdmondsKarp.ShortestPath.pathEps_bounds {V : Type} [Fintype V] [DecidableEq V] (N : Network V)
    (f : V → V → ℝ) (P : List V) (hf : IsFlow N f) (hP : IsAugPath N f P) :
    0 < pathEps N f P ∧
    (∀ e ∈ pathArcs P, pathEps N f P ≤ stepEps N f e.1 e.2) ∧
    ∃ u v, IsBottleneck N f P u v := by sorry
