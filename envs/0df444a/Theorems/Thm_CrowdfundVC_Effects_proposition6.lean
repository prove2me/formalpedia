-- Prove2me | Theorems.Thm_CrowdfundVC_Effects_proposition6
-- name    : CrowdfundVC.Effects.proposition6
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-14T04:10:37.078977+00:00
-- url     : https://prove2.me/theorems/378c3c60-1e01-4cf6-b593-53cd19068a77
-- title:
--   Proposition 6, PDF p. 21 — the crowdfunding option lowers the expected VC investment level iff e1 ≥ R0 and Δa > 0, and otherwise raises it
-- statement:
--   Compare the expected VC investment level, with respect to the unconditional belief $P(\theta = s) = P(\theta = f) = \tfrac12$, in the two settings. Without crowdfunding the startup offers $\alpha^o = R_0/e_1$ (Proposition 1) and the level is $\kappa(\alpha^o e_1, \alpha^o e_2, R_0)$. With crowdfunding it offers $\alpha^c$ (Proposition 4), and the level is computed along VC$_1$'s decisions: $\kappa(v_1, v_2, R_0)$ if VC$_1$ invests at $t_0$, otherwise the average of the post-campaign levels after $S$ and $F$ with probabilities $P(S\mid\tfrac12)$, $P(F\mid\tfrac12)$.
--
--   Assume $0 \le R_f < R_0 < R_s$, $0 < K < R_0$, $0 \le \rho \le 1$, $0 \le \beta < 1$, $0 \le p_2 \le p_1 \le 1$, $0 \le p_a \le 1$, $e_a > 0$ and Assumption (I), $\tilde e_1|S \ge R_0$. Write $I^o$ and $I^c$ for the two levels. Then:
--
--   1. if $\rho > 0$, $p_1 < 1$, $e_1 \ge R_0$ and $\Delta_a > 0$, crowdfunding reduces the level: $I^c < I^o$;
--   2. if $e_1 \ge R_0$ and $\Delta_a \le 0$, crowdfunding raises the level: $I^o \le I^c$;
--   3. if $e_1 < R_0$, there is no investment without crowdfunding at any share — $\kappa(\alpha e_1, \alpha e_2, R_0) = 0$ for every $\alpha \in [0,1]$ — while $I^c > 0$.
--
--   In short, when $\rho > 0$ and $p_1 < 1$,
--   $$I^c < I^o \iff e_1 \ge R_0 \text{ and } \Delta_a > 0 .$$
--   This is the paper's main finding on VC investment: crowdfunding lowers the expected investment exactly when a startup that VC$_1$ would fund anyway prefers to wait for the campaign, and otherwise it raises it.
--
--   **Formalization Note** "Raises" is weak in case 2: at $\beta = 0$ both levels equal $R_0$; it is strict in case 3. The hypotheses $\beta < 1$, $e_a > 0$ and $0 \le R_f$ (on the whole theorem) and $\rho > 0$, $p_1 < 1$ (on case 1 only) are not in the paper and are each needed: at $\beta = 1$ VC$_1$'s threshold is not $\alpha_0$; with $R_f < 0$ the threshold can be negative; with $e_a = 0$ the share $\alpha^c$ can exceed $1$; at $\rho = 0$ (or $p_1 = 1$) VC$_1$ need not wait at $\alpha^c$ and $I^c = I^o$ in case 1. The paper's case "$e_1 < R_0$ or $\Delta_a \le 0$" is split into cases 2 and 3.
-- source:
--   Hu, Jin & Keppo, The Crowdfunding Effects on Venture Capital Investment, SSRN author manuscript (abstract 3512638, 2024-03-15; Management Science DOI 10.1287/mnsc.2022.00994), PDF p. 21, Proposition 6; proof Online Appendix D, PDF pp. 52–53 (OA pp. 25–26)

import Mathlib
import Definitions.Def_CrowdfundVC_Effects_Model

namespace CrowdfundVC.Effects

/-- Proposition 6 (p. 21). If `e1 ≥ R0` and `Δa > 0` (and the signal is informative, `ρ > 0`, and
`p1 < 1`), the crowdfunding option strictly reduces the expected VC investment level; if `e1 ≥ R0`
and `Δa ≤ 0`, it (weakly) raises it; if `e1 < R0`, there is no investment
without crowdfunding at any share in `[0, 1]`, and the expected level with crowdfunding is
positive. Without crowdfunding the startup offers `αᵒ = R0/e1` (Proposition 1), with crowdfunding `αᶜ`
(Proposition 4). -/
theorem proposition6 (P : Params)
    (hRf0 : 0 ≤ P.Rf) (hRfR0 : P.Rf < P.R0) (hR0Rs : P.R0 < P.Rs) (hK0 : 0 < P.K)
    (hKR0 : P.K < P.R0) (hρ0 : 0 ≤ P.ρ) (hρ1 : P.ρ ≤ 1) (hβ0 : 0 ≤ P.β) (hβ1 : P.β < 1)
    (hp2 : 0 ≤ P.p2) (hp12 : P.p2 ≤ P.p1) (hp1 : P.p1 ≤ 1) (hpa0 : 0 ≤ P.pa) (hpa1 : P.pa ≤ 1)
    (hea : 0 < ea P) (hI : P.R0 ≤ e1S P) :
    (0 < P.ρ → P.p1 < 1 →
      P.R0 ≤ e1 P → 0 < deltaA P → invLevelCF P (alphaC P) < invLevelNoCF P (P.R0 / e1 P)) ∧
    (P.R0 ≤ e1 P → deltaA P ≤ 0 → invLevelNoCF P (P.R0 / e1 P) ≤ invLevelCF P (alphaC P)) ∧
    (e1 P < P.R0 →
      (∀ α : ℝ, 0 ≤ α → α ≤ 1 → invLevelNoCF P α = 0) ∧ 0 < invLevelCF P (alphaC P)) := by sorry

end CrowdfundVC.Effects
