-- Prove2me | Theorems.Thm_CrowdfundVC_Effects_investment_level_cf
-- name    : CrowdfundVC.Effects.investment_level_cf
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-14T04:10:46.45948+00:00
-- url     : https://prove2.me/theorems/b009021b-1aaf-4862-a964-a6180501987d
-- title:
--   Proof of Proposition 6, PDF p. 52 — the expected investment level with crowdfunding is βα0e1 + (1 − β)R0 if Δa ≤ 0 and (R0 − K)/2 if Δa > 0
-- statement:
--   Under the standing assumptions ($0 \le R_f < R_0 < R_s$, $0 < K < R_0$, $0 \le \rho \le 1$, $0 \le \beta < 1$, $0 \le p_2 \le p_1 \le 1$, $0 \le p_a \le 1$, $\tilde e_1|S \ge R_0$) and $e_a > 0$, the expected VC investment level with crowdfunding, with respect to the unconditional belief $P(\theta = s) = P(\theta = f) = \tfrac12$ and at the startup's optimal share $\alpha^c$ of Proposition 4, is
--   $$I^c = \begin{cases}\beta\alpha_0 e_1 + (1-\beta)R_0 & \text{if } \Delta_a \le 0,\\[2pt] \dfrac{R_0 - K}{2} & \text{if } \Delta_a > 0.\end{cases}$$
--
--   Here the expected level is computed along VC$_1$'s decisions: $\kappa(v_1, v_2, R_0)$ if VC$_1$ invests at $t_0$, and otherwise the average over the signals, with probabilities $P(S\mid\tfrac12)$ and $P(F\mid\tfrac12)$, of the levels at $t_1$. This closed form is the first step of the paper's proof of Proposition 6.
--
--   **Formalization Note** The hypotheses $\rho > 0$ and $p_1 < 1$ are added to the case $\Delta_a > 0$ only (the case $\Delta_a \le 0$ is stated without them): they make $\tilde e_1|S > e_1$, so that VC$_1$ really waits at $\alpha^c = R_0/\tilde e_1|S$ when $\Delta_a > 0$ (the paper's proof uses this without saying so; at $\rho = 0$ one can have $\alpha^c = \alpha_0 = 1$, VC$_1$ invests at $t_0$ and the level is $R_0$). $e_a > 0$, $\beta < 1$ and $0 \le R_f$ are added as for Proposition 4.
-- source:
--   Hu, Jin & Keppo, The Crowdfunding Effects on Venture Capital Investment, SSRN author manuscript (abstract 3512638, 2024-03-15; Management Science DOI 10.1287/mnsc.2022.00994), Online Appendix D, proof of Proposition 6, PDF p. 52 (OA p. 25), display of Ic

import Mathlib
import Definitions.Def_CrowdfundVC_Effects_Model

namespace CrowdfundVC.Effects

/-- The expected VC investment level with crowdfunding (proof of Proposition 6, Online Appendix D,
PDF p. 52): at `αᶜ`, it is `β α0 e1 + (1 − β) R0` if `Δa ≤ 0`, and `(R0 − K)/2` if `Δa > 0`
(the latter when `ρ > 0` and `p1 < 1`, so that VC1 waits at `αᶜ = R0/ẽ1|S`). -/
theorem investment_level_cf (P : Params)
    (hRf0 : 0 ≤ P.Rf) (hRfR0 : P.Rf < P.R0) (hR0Rs : P.R0 < P.Rs) (hK0 : 0 < P.K)
    (hKR0 : P.K < P.R0) (hρ0 : 0 ≤ P.ρ) (hρ1 : P.ρ ≤ 1) (hβ0 : 0 ≤ P.β) (hβ1 : P.β < 1)
    (hp2 : 0 ≤ P.p2) (hp12 : P.p2 ≤ P.p1) (hp1 : P.p1 ≤ 1) (hpa0 : 0 ≤ P.pa) (hpa1 : P.pa ≤ 1)
    (hea : 0 < ea P) (hI : P.R0 ≤ e1S P) :
    (deltaA P ≤ 0 → invLevelCF P (alphaC P) = P.β * alpha0 P * e1 P + (1 - P.β) * P.R0) ∧
    (0 < P.ρ → P.p1 < 1 → 0 < deltaA P → invLevelCF P (alphaC P) = (P.R0 - P.K) / 2) := by sorry

end CrowdfundVC.Effects
