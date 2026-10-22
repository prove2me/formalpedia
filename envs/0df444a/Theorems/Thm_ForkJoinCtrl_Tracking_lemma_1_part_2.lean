-- Prove2me | Theorems.Thm_ForkJoinCtrl_Tracking_lemma_1_part_2
-- name    : ForkJoinCtrl.Tracking.lemma_1_part_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-21T05:14:29.675702+00:00
-- url     : https://prove2.me/theorems/29e89e35-1005-48a9-b24a-21d76536f689
-- title:
--   Lemma 1 Part 2, p. 12 — the optimal value z(b) of LP (18) is Lipschitz in b with respect to |·|∞
-- statement:
--   The optimal value $z(b)$ of the LP (18) maps $\mathbb R^{a_2}_+$ into $\mathbb R_+$, and there is a constant $C_1>0$, depending only on the network data (the objective coefficients and the left-hand-side parameters of the constraints), such that for all $b^{(1)},b^{(2)}\in\mathbb R^{a_2}_+$
--
--   $$|z(b^{(1)})-z(b^{(2)})|\le C_1\,|b^{(1)}-b^{(2)}|_\infty .$$
--
--   Lipschitz continuity of $z$ makes the process map $f\mapsto z(f(\cdot))$ continuous, which is what transfers the diffusion limit of Proposition 2 to the cost.
--
--   **Formalization Note** $|\cdot|_\infty$ is Mathlib's norm on the parameter pair (the maximum absolute coordinate). The constant is chosen after the network and before $b^{(1)},b^{(2)}$.
-- source:
--   Özkan, Control of Fork-Join Processing Networks with Multiple Job Types and Parallel Shared Resources, arXiv:2002.01496v1, p. 12, Lemma 1 Part 2

import Mathlib
import Definitions.Def_ForkJoinCtrl_Tracking_LP

namespace ForkJoinCtrl.Tracking

theorem lemma_1_part_2 (N : Network) :
    (∀ b : LPParam N, b.Nonneg → 0 ≤ z N b) ∧
    ∃ C1 : ℝ, 0 < C1 ∧ ∀ b1 b2 : LPParam N, b1.Nonneg → b2.Nonneg →
      |z N b1 - z N b2| ≤ C1 * ‖b1 - b2‖ := by sorry

end ForkJoinCtrl.Tracking
