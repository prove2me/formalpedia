-- Prove2me | Theorems.Thm_CrowdfundVC_Effects_proposition2_i
-- name    : CrowdfundVC.Effects.proposition2_i
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-14T04:10:47.195516+00:00
-- url     : https://prove2.me/theorems/acab5616-792d-4f90-a238-0a71e41f1f46
-- title:
--   Proposition 2(i), PDF p. 14 — with crowdfunding, VC1 invests at t0 iff α ≥ α0
-- statement:
--   With the crowdfunding option, VC$_1$ invests at the pre-crowdfunding time $t_0$ when it can meet the requirement, $v_1 = \alpha e_1 \ge R_0$, and its value of waiting $\Delta_1 = \tilde\pi_1 - \pi_1$ is nonpositive (ties are resolved in favour of investing now). Let
--   $$T_1 = \frac{R_0}{e_1 - P(S\mid p_1)\frac{R_0-K}{R_0}(\tilde e_1|S - \tilde e_2|S)}, \qquad T_2 = \frac{R_0 - P(S\mid p_1)(R_0-K)}{e_1 - P(S\mid p_1)\,\tilde e_1|S\,\frac{R_0-K}{R_0}},$$
--   and $\alpha_0 = T_2$ if $\tilde e_2|S \le R_0/T_2$, $\alpha_0 = T_1$ otherwise.
--
--   Under the standing assumptions ($0 \le R_f < R_0 < R_s$, $0 < K < R_0$, $0 \le \rho \le 1$, $0 \le \beta < 1$, $0 \le p_2 \le p_1 \le 1$, $0 \le p_a \le 1$, $\tilde e_1|S \ge R_0$), for every equity share $\alpha \in [0,1]$:
--   $$\text{VC}_1 \text{ invests at } t_0 \iff \alpha \ge \alpha_0 .$$
--
--   This identifies the printed closed form $\alpha_0$ as the minimum equity share that induces pre-crowdfunding investment; every later result about the startup's choice and the investment level is built on it.
--
--   **Formalization Note** The decision "invest at $t_0$" includes $v_1 \ge R_0$, as in the paper's proof ("VC1 chooses to invest at time $t_0$ if and only if $\Delta_1 \le 0$ and $v_1 \ge R_0$", PDF p. 49); the statement's parenthesis "(i.e., $\Delta_1 \le 0$)" omits it. The negotiation power is restricted to $\beta < 1$: at $\beta = 1$ both surpluses vanish, $\Delta_1 = 0$, and VC$_1$ invests at every $\alpha \ge R_0/e_1$, which can be below $\alpha_0$. $0 \le R_f$ is added as for every item.
-- source:
--   Hu, Jin & Keppo, The Crowdfunding Effects on Venture Capital Investment, SSRN author manuscript (abstract 3512638, 2024-03-15; Management Science DOI 10.1287/mnsc.2022.00994), PDF p. 14, Proposition 2(i); proof Online Appendix D, PDF pp. 44–50 (OA pp. 17–23)

import Mathlib
import Definitions.Def_CrowdfundVC_Effects_Model

namespace CrowdfundVC.Effects

/-- Proposition 2(i) (p. 14). For every equity share `α ∈ [0, 1]`, VC1 invests at `t0` (it can,
`v1 ≥ R0`, and its value of waiting is `Δ1 ≤ 0`) if and only if `α ≥ α0`, with `α0` the printed closed form. -/
theorem proposition2_i (P : Params)
    (hRf0 : 0 ≤ P.Rf) (hRfR0 : P.Rf < P.R0) (hR0Rs : P.R0 < P.Rs) (hK0 : 0 < P.K)
    (hKR0 : P.K < P.R0) (hρ0 : 0 ≤ P.ρ) (hρ1 : P.ρ ≤ 1) (hβ0 : 0 ≤ P.β) (hβ1 : P.β < 1)
    (hp2 : 0 ≤ P.p2) (hp12 : P.p2 ≤ P.p1) (hp1 : P.p1 ≤ 1) (hpa0 : 0 ≤ P.pa) (hpa1 : P.pa ≤ 1)
    (hI : P.R0 ≤ e1S P) :
    ∀ α : ℝ, 0 ≤ α → α ≤ 1 → (investsAt0 P α ↔ alpha0 P ≤ α) := by sorry

end CrowdfundVC.Effects
