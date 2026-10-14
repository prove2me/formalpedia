-- Prove2me | Theorems.Thm_CrowdfundVC_Effects_startup_objective
-- name    : CrowdfundVC.Effects.startup_objective
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-14T04:10:44.927782+00:00
-- url     : https://prove2.me/theorems/20205df8-096f-45c0-a1fb-17c35ca62b93
-- title:
--   §5.2 display, PDF p. 17 — the startup's anticipated payoff with crowdfunding equals the paper's two-indicator objective
-- statement:
--   Under the standing assumptions ($0 \le R_f < R_0 < R_s$, $0 < K < R_0$, $0 \le \rho \le 1$, $0 \le \beta < 1$, $0 \le p_2 \le p_1 \le 1$, $0 \le p_a \le 1$, $\tilde e_1|S \ge R_0$), for every equity share $\alpha \in [0,1]$ the startup's anticipated payoff with crowdfunding, computed from VC$_1$'s responses (invest at $t_0$, or wait and invest after $S$ or after $F$), equals
--   $$\mathbb I_{\{\alpha_0 \le \alpha \le 1\}}(1-\alpha)e_a + \mathbb I_{\{R_0/\tilde e_1|S \le \alpha < \alpha_0\}}\Big(1 - \frac{R_0-K}{R_0}\alpha\Big)\tilde e_a|S\cdot P(S\mid p_a).$$
--
--   This is the optimization problem the paper writes for the startup "in anticipation of VC$_1$'s optimal investment strategy"; the statement certifies that the paper's objective is the startup's actual payoff in the model. Proposition 4 maximizes it.
--
--   **Formalization Note** The hypotheses $\beta < 1$ and $0 \le R_f$ are added as for Proposition 2.
-- source:
--   Hu, Jin & Keppo, The Crowdfunding Effects on Venture Capital Investment, SSRN author manuscript (abstract 3512638, 2024-03-15; Management Science DOI 10.1287/mnsc.2022.00994), PDF p. 17, §5.2, unnumbered display

import Mathlib
import Definitions.Def_CrowdfundVC_Effects_Model

namespace CrowdfundVC.Effects

/-- The startup's problem with crowdfunding (§5.2 display, p. 17): for `α ∈ [0, 1]`, the startup's
anticipated payoff equals `𝕀{α0 ≤ α ≤ 1}(1 − α)ea + 𝕀{R0/ẽ1|S ≤ α < α0}(1 − ((R0 − K)/R0)α) ẽa|S · P(S|pa)`. -/
theorem startup_objective (P : Params)
    (hRf0 : 0 ≤ P.Rf) (hRfR0 : P.Rf < P.R0) (hR0Rs : P.R0 < P.Rs) (hK0 : 0 < P.K)
    (hKR0 : P.K < P.R0) (hρ0 : 0 ≤ P.ρ) (hρ1 : P.ρ ≤ 1) (hβ0 : 0 ≤ P.β) (hβ1 : P.β < 1)
    (hp2 : 0 ≤ P.p2) (hp12 : P.p2 ≤ P.p1) (hp1 : P.p1 ≤ 1) (hpa0 : 0 ≤ P.pa) (hpa1 : P.pa ≤ 1)
    (hI : P.R0 ≤ e1S P) :
    ∀ α : ℝ, 0 ≤ α → α ≤ 1 →
      payoffCF P α =
        (if alpha0 P ≤ α ∧ α ≤ 1 then (1 - α) * ea P else 0) +
        (if P.R0 / e1S P ≤ α ∧ α < alpha0 P then
          (1 - (P.R0 - P.K) / P.R0 * α) * eaS P * probS P P.pa else 0) := by sorry

end CrowdfundVC.Effects
