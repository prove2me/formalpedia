-- Prove2me | Theorems.Thm_CrowdfundVC_Effects_proposition3_i
-- name    : CrowdfundVC.Effects.proposition3_i
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-14T04:11:29.811718+00:00
-- url     : https://prove2.me/theorems/11ae398f-48f1-494c-8147-715c49b8544c
-- title:
--   Proposition 3(i), PDF p. 16 — R0/e1 ≤ α0 ≤ R0/e2
-- statement:
--   Under the standing assumptions ($0 \le R_f < R_0 < R_s$, $0 < K < R_0$, $0 \le \rho \le 1$, $0 \le \beta \le 1$, $0 \le p_2 \le p_1 \le 1$, $0 \le p_a \le 1$, $\tilde e_1|S \ge R_0$), the threshold $\alpha_0$ of Proposition 2 satisfies
--   $$\frac{R_0}{e_1} \le \alpha_0 \le \frac{R_0}{e_2}.$$
--
--   The lower bound says that crowdfunding raises the share needed for pre-crowdfunding investment above the no-crowdfunding share (strategic delay). The upper bound says that at $\alpha_0$ VC$_2$'s valuation $\alpha_0 e_2$ does not exceed $R_0$, so the investment level at $\alpha_0$ is $\beta\alpha_0 e_1 + (1-\beta)R_0$; both facts are used to compare investment levels in Proposition 6.
--
--   **Formalization Note** The upper bound is stated as $\alpha_0 e_2 \le R_0$. When $e_2 = 0$ (possible with $p_2 = 0$ and $R_f = 0$) the page's $R_0/e_2$ is $+\infty$, while Lean's $R_0/0 = 0$ would make the divided form false; the multiplied form is what the proof of Proposition 6 uses ("$v_2 \le R_0$"). $0 \le R_f$ is added as for every item.
-- source:
--   Hu, Jin & Keppo, The Crowdfunding Effects on Venture Capital Investment, SSRN author manuscript (abstract 3512638, 2024-03-15; Management Science DOI 10.1287/mnsc.2022.00994), PDF p. 16, Proposition 3(i); proof Online Appendix D, PDF pp. 50–51 (OA pp. 23–24)

import Mathlib
import Definitions.Def_CrowdfundVC_Effects_Model

namespace CrowdfundVC.Effects

/-- Proposition 3(i) (p. 16): `R0/e1 ≤ α0 ≤ R0/e2`, the upper bound written as `α0 e2 ≤ R0`
(the page's `R0/e2` is `+∞` when `e2 = 0`). -/
theorem proposition3_i (P : Params)
    (hRf0 : 0 ≤ P.Rf) (hRfR0 : P.Rf < P.R0) (hR0Rs : P.R0 < P.Rs) (hK0 : 0 < P.K)
    (hKR0 : P.K < P.R0) (hρ0 : 0 ≤ P.ρ) (hρ1 : P.ρ ≤ 1) (hβ0 : 0 ≤ P.β) (hβ1 : P.β ≤ 1)
    (hp2 : 0 ≤ P.p2) (hp12 : P.p2 ≤ P.p1) (hp1 : P.p1 ≤ 1) (hpa0 : 0 ≤ P.pa) (hpa1 : P.pa ≤ 1)
    (hI : P.R0 ≤ e1S P) :
    P.R0 / e1 P ≤ alpha0 P ∧ alpha0 P * e2 P ≤ P.R0 := by sorry

end CrowdfundVC.Effects
