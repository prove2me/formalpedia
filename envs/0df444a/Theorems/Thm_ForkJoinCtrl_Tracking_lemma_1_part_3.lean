-- Prove2me | Theorems.Thm_ForkJoinCtrl_Tracking_lemma_1_part_3
-- name    : ForkJoinCtrl.Tracking.lemma_1_part_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-21T05:14:44.321534+00:00
-- url     : https://prove2.me/theorems/d91f8418-b920-463a-b104-5e9ea5fa5efe
-- title:
--   Lemma 1 Part 3, p. 12 — QP (19) has a unique optimal solution, and its q-part is Lipschitz in b
-- statement:
--   For every $b\in\mathbb R^{a_2}_+$ the QP (19) — minimize $\sum_j y_j^2+\sum_j\sum_{i\in\mathcal I_j}q_{ij}^2$ over the LP-feasible points with $\sum_j h_jy_j\le z(b)$ — has a unique optimal solution. Moreover there is $C_2>0$, depending only on the network data, such that if $(y^{(1)},q^{(1)})$ and $(y^{(2)},q^{(2)})$ are the optimal solutions at $b^{(1)},b^{(2)}\in\mathbb R^{a_2}_+$, then
--
--   $$\max_{j\in\mathcal J,\,i\in\mathcal I_j}|q^{(1)}_{ij}-q^{(2)}_{ij}|\le C_2\,|b^{(1)}-b^{(2)}|_\infty .$$
--
--   The QP selects, among possibly many LP optima, one that moves continuously with the state; this is what the tracking policy follows.
--
--   **Formalization Note** Only the $q$-part is bounded, as in the paper. Non-incident entries $q_{ij}$ are pinned to $0$, so uniqueness is uniqueness of the paper's decision vector.
-- source:
--   Özkan, Control of Fork-Join Processing Networks with Multiple Job Types and Parallel Shared Resources, arXiv:2002.01496v1, p. 12, Lemma 1 Part 3

import Mathlib
import Definitions.Def_ForkJoinCtrl_Tracking_LP

namespace ForkJoinCtrl.Tracking

theorem lemma_1_part_3 (N : Network) :
    (∀ b : LPParam N, b.Nonneg → ∃! x : LPVar N, QPOpt N b x) ∧
    ∃ C2 : ℝ, 0 < C2 ∧ ∀ (b1 b2 : LPParam N) (x1 x2 : LPVar N), b1.Nonneg → b2.Nonneg →
      QPOpt N b1 x1 → QPOpt N b2 x2 → ∀ i j, N.P i j = true →
        |x1.q i j - x2.q i j| ≤ C2 * ‖b1 - b2‖ := by sorry

end ForkJoinCtrl.Tracking
