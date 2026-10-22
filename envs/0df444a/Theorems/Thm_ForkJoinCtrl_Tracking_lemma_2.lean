-- Prove2me | Theorems.Thm_ForkJoinCtrl_Tracking_lemma_2
-- name    : ForkJoinCtrl.Tracking.lemma_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-21T05:14:48.148792+00:00
-- url     : https://prove2.me/theorems/5bd80865-86bd-4b42-8b38-604bcb5b2db6
-- title:
--   Lemma 2, p. 13 — the QP-selected LP solution process moves by at most C2 times the movement of its parameter process
-- statement:
--   There is a constant $C_2>0$, depending only on the network data, with the following property. Let $(b(t),t\ge0)$ be a nonnegative càdlàg parameter process and let $(\tilde y(t),\tilde q(t))$ be the càdlàg optimal solution process of the QP (19) at $b(t)$ for every $t\ge 0$ (the optimal solution process of the LP (18) selected by the QP (19)). Then for all $s,t\ge0$
--
--   $$\max_{j\in\mathcal J,\,i\in\mathcal I_j}|\tilde q_{ij}(s)-\tilde q_{ij}(t)|\le C_2\,|b(s)-b(t)|_\infty .$$
--
--   This is the pathwise form of Lemma 1 Part 3 used to show that the tracking target $q^{*,r}$ moves little within a review period.
--
--   **Formalization Note** The paper puts both the parameter path and the selected solution path in càdlàg path spaces. Lean uses nonnegative real time and states càdlàg continuity for $b$, $\tilde y$, and $\tilde q$. As a separate item it cannot refer to the constant of Lemma 1 Part 3, so $C_2$ is existentially quantified here.
-- source:
--   Özkan, Control of Fork-Join Processing Networks with Multiple Job Types and Parallel Shared Resources, arXiv:2002.01496v1, p. 13, Lemma 2

import Mathlib
import Definitions.Def_ForkJoinCtrl_Tracking_LP
import Definitions.Def_PuhaWardFluid_Limit_Paths

open scoped NNReal

namespace ForkJoinCtrl.Tracking

theorem lemma_2 (N : Network) :
    ∃ C2 : ℝ, 0 < C2 ∧ ∀ (b : ℝ≥0 → LPParam N) (x : ℝ≥0 → LPVar N),
      PuhaWardFluid.Limit.IsCadlag b →
      PuhaWardFluid.Limit.IsCadlag (fun t => (x t).y) →
      PuhaWardFluid.Limit.IsCadlag (fun t => (x t).q) →
      (∀ t, (b t).Nonneg) → (∀ t, QPOpt N (b t) (x t)) →
      ∀ s t : ℝ≥0, ∀ i j, N.P i j = true →
        |(x s).q i j - (x t).q i j| ≤ C2 * ‖b s - b t‖ := by sorry

end ForkJoinCtrl.Tracking
