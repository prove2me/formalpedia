-- Prove2me | Theorems.Thm_DuffieHedge_Optimal_proposition_1
-- name    : DuffieHedge.Optimal.proposition_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T09:17:54.770695+00:00
-- url     : https://prove2.me/theorems/61b0949e-d196-404a-a0b7-89a6e1261599
-- title:
--   Proposition 1 — the feedback futures strategy $\Phi(G^*)$ defined by (9)–(11) solves problem (3)
-- statement:
--   Work in the futures-hedging market of Duffie and Richardson under the standing hypotheses: a committed asset $dS_t=\mu_tS_t\,dt+\sigma_tS_t\,dB_t$ and a futures price $dF_t=m_tF_t\,dt+v_tF_t\,d\xi_t$ with bounded measurable coefficients, $|v|$ bounded away from $0$ and correlation $\rho_t\in[-1,1]$. Fix a commitment of $k$ units of $S$ at $T$ and a target level $L$. Let $Z$ be the tracking process (9), $\Phi$ the feedback map (11), and $G^*$ any solution of
--
--   $$dG^*_t=\Phi(G^*_t)\,dF_t,\qquad G^*_0=0\quad(10).$$
--
--   Then the futures strategy $\varphi_t=\Phi(G^*_t)$ solves problem (3):
--
--   $$E\big[(kS_T+G(\varphi)_T-L)^2\big]=\min_{\theta\in\Theta}E\big[(kS_T+G(\theta)_T-L)^2\big].$$
--
--   This is the main result of the paper: the mean-square optimal hedge with futures is a feedback rule in the observable gains to date $G^*_t$ and the observable price $S_t$ (through $Z_t$), valid for every target $L$.
--
--   **Formalization Note.** "Defined by (9)–(11)" is read as: for every solution $G^*$ of (10), where a solution includes that $\Phi(G^*)$ is a trading strategy — the paper takes this for granted. Such a solution exists by the companion milestone (§3.3, p. 5). Optimality is over all versions of the gains and all progressively measurable $\theta$ with $E\int_0^T\theta_t^2F_t^2\,dt<\infty$; the objective is a lower integral in $[0,\infty]$.
-- source:
--   Duffie and Richardson, Mean-Variance Hedging in Continuous Time, Ann. Appl. Probab. 1(1) (1991), Proposition 1, p. 5

import Mathlib
import Definitions.Def_DuffieHedge_Optimal_Basic

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace DuffieHedge.Optimal

/-- Proposition 1 (p. 5): for every solution `G*` of (10), the feedback futures strategy
`φ_t = Φ(G*_t)` defined by (9)–(11) solves problem (3). -/
theorem proposition_1 {Ω : Type*} [MeasurableSpace Ω] (M : Market Ω) (hM : M.Standing)
    (k L : ℝ) (Gs : ℝ≥0 → Ω → ℝ) (hGs : M.SolvesEq10 k L Gs) :
    M.SolvesP3 k L (M.feedback k L Gs) := by sorry

end DuffieHedge.Optimal
