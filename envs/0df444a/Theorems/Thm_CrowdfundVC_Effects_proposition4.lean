-- Prove2me | Theorems.Thm_CrowdfundVC_Effects_proposition4
-- name    : CrowdfundVC.Effects.proposition4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-14T04:10:38.582191+00:00
-- url     : https://prove2.me/theorems/9c4d9ca5-16c0-4199-b291-d0d8646af821
-- title:
--   Proposition 4, PDF p. 18 — αᶜ = α0 if Δa ≤ 0 and R0/ẽ1|S if Δa > 0 is the startup's optimal share
-- statement:
--   Let $\pi_a = (1-\alpha_0)e_a$, $\tilde\pi_a = \big(1 - \frac{R_0-K}{\tilde e_1|S}\big)\tilde e_a|S\cdot P(S\mid p_a)$, and $\Delta_a = \tilde\pi_a - \pi_a$ (the startup's value of waiting), and set
--   $$\alpha^c = \begin{cases}\alpha_0 & \text{if } \Delta_a \le 0,\\ R_0/\tilde e_1|S & \text{if } \Delta_a > 0.\end{cases}$$
--
--   Under the standing assumptions ($0 \le R_f < R_0 < R_s$, $0 < K < R_0$, $0 \le \rho \le 1$, $0 \le \beta < 1$, $0 \le p_2 \le p_1 \le 1$, $0 \le p_a \le 1$, $\tilde e_1|S \ge R_0$) and $e_a > 0$, the share $\alpha^c$ lies in $[0,1]$ and maximizes the startup's anticipated payoff with crowdfunding over all $\alpha \in [0,1]$.
--
--   The startup either offers a high share to induce investment before the campaign or a low one to induce investment after a successful campaign; $\Delta_a$ decides which. This optimal share is the one at which Proposition 6 evaluates the investment level.
--
--   **Formalization Note** "Optimal" is a global maximizer over $[0,1]$; at $\Delta_a = 0$ both candidates are optimal and the paper's rule selects $\alpha_0$. The hypothesis $e_a > 0$ is added: with $p_a = R_f = 0$ all payoffs vanish, $\Delta_a = 0$, and $\alpha^c = \alpha_0$ can exceed $1$. The hypotheses $\beta < 1$ and $0 \le R_f$ are added as for Proposition 2.
-- source:
--   Hu, Jin & Keppo, The Crowdfunding Effects on Venture Capital Investment, SSRN author manuscript (abstract 3512638, 2024-03-15; Management Science DOI 10.1287/mnsc.2022.00994), PDF p. 18, Proposition 4 (with πa, π̃a displayed on p. 18); proof Online Appendix D, PDF p. 51 (OA p. 24)

import Mathlib
import Definitions.Def_CrowdfundVC_Effects_Model

namespace CrowdfundVC.Effects

/-- Proposition 4 (p. 18). The share `αᶜ` (`α0` if `Δa ≤ 0`, `R0/ẽ1|S` if `Δa > 0`) lies in `[0, 1]`
and maximizes the startup's anticipated payoff with crowdfunding over `[0, 1]`. -/
theorem proposition4 (P : Params)
    (hRf0 : 0 ≤ P.Rf) (hRfR0 : P.Rf < P.R0) (hR0Rs : P.R0 < P.Rs) (hK0 : 0 < P.K)
    (hKR0 : P.K < P.R0) (hρ0 : 0 ≤ P.ρ) (hρ1 : P.ρ ≤ 1) (hβ0 : 0 ≤ P.β) (hβ1 : P.β < 1)
    (hp2 : 0 ≤ P.p2) (hp12 : P.p2 ≤ P.p1) (hp1 : P.p1 ≤ 1) (hpa0 : 0 ≤ P.pa) (hpa1 : P.pa ≤ 1)
    (hea : 0 < ea P) (hI : P.R0 ≤ e1S P) :
    0 ≤ alphaC P ∧ alphaC P ≤ 1 ∧
      ∀ α : ℝ, 0 ≤ α → α ≤ 1 → payoffCF P α ≤ payoffCF P (alphaC P) := by sorry

end CrowdfundVC.Effects
