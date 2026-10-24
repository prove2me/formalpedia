-- Prove2me | Theorems.Thm_DirectedSearch_Approx_proposition_4_4
-- name    : DirectedSearch.Approx.proposition_4_4
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-15T09:04:07.957979+00:00
-- url     : https://prove2.me/theorems/0a26bdd5-2c34-41d7-b388-f7b7e4e9a030
-- title:
--   Proposition 4.4, p. 20 — the platform's first-best problem is equivalent to LP (7)
-- statement:
--   Consider a directed-search market satisfying the standing assumptions. The platform's first-best problem — maximize the welfare (6) with free pairwise thresholds $\tau_{mw}$ subject to (6a)–(6d), (6f) — is equivalent to the linear program
--   $$\max_{\beta\ge0}\ 2\sum_{m\in\mathcal M}\sum_{w\in\mathcal W}\rho_{mw}\beta_{mw}\quad\text{s.t.}\quad \sum_{w}\beta_{mw}\le\alpha_m\ \ \forall m,\qquad \sum_m\beta_{mw}\le\alpha_w\ \ \forall w,$$
--   where $\rho_{mw}=\max_{\tau\ge0}\int_\tau^\infty u\,dF_{mw}/(\delta+\int_\tau^\infty dF_{mw})$, in the following sense:
--
--   1. both problems attain their maxima, and the two optimal values are equal;
--   2. every feasible $\beta$ corresponds to a first-best feasible choice of $\lambda,\eta,\xi,\tau_{mw}$ with the same objective value.
--
--   This reduces the first best to a generalized assignment problem, the starting point of the approximation.
--
--   **Formalization Note.** "The same optimal objective value" is stated as: a common value $v$ is the greatest element of both sets of achievable objective values. $\beta\ge0$ is part of LP feasibility (implicit in the paper through (9)).
-- source:
--   Immorlica, Lucier, Manshadi, Wei, Designing Approximately Optimal Search on Matching Platforms, arXiv:2102.09017v2, p. 20, Proposition 4.4, LP (7)/(7a)/(7b)

import Mathlib
import Definitions.Def_DirectedSearch_Approx_Setting

namespace DirectedSearch.Approx
theorem proposition_4_4 {M W : Type} [Fintype M] [Fintype W] [DecidableEq M] [DecidableEq W]
    (mk : Market M W) (hmk : mk.Standing) :
    (∃ v : ℝ, IsGreatest (fbWelfare mk '' {Q | FirstBestFeasible mk Q}) v ∧
      IsGreatest (lpObj mk '' {β | LPFeasible mk β}) v) ∧
    (∀ β : M → W → ℝ, LPFeasible mk β →
      ∃ Q : FBProfile M W, FirstBestFeasible mk Q ∧ fbWelfare mk Q = lpObj mk β) := by sorry
end DirectedSearch.Approx
