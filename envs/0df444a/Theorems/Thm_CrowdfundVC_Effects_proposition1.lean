-- Prove2me | Theorems.Thm_CrowdfundVC_Effects_proposition1
-- name    : CrowdfundVC.Effects.proposition1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-14T04:10:35.246327+00:00
-- url     : https://prove2.me/theorems/5f92c8b5-0e5a-4f3f-9496-127844dfac1e
-- title:
--   Proposition 1, PDF p. 12 — without crowdfunding: no investment if e1 < R0; otherwise αᵒ = R0/e1 is optimal and VC1 invests R0
-- statement:
--   Consider the setting without a crowdfunding platform, where VC$_1$ invests at the equity share $\alpha$ iff its valuation $v_1 = \alpha e_1$ reaches the requirement $R_0$, the startup's payoff is $(1-\alpha)e_a$ if VC$_1$ invests and $0$ otherwise, and the investment level is $\kappa(\alpha e_1, \alpha e_2, R_0)$.
--
--   Assume the standing assumptions of the paper: $0 \le R_f < R_0 < R_s$, $0 < K < R_0$, $0 \le \rho \le 1$, $0 \le \beta \le 1$, $0 \le p_2 \le p_1 \le 1$, $0 \le p_a \le 1$, and Assumption (I), $\tilde e_1|S \ge R_0$. Then:
--
--   1. If $e_1 < R_0$, then for every $\alpha \in [0,1]$ VC$_1$ does not invest and the investment level is $0$.
--   2. If $e_1 \ge R_0$, then $\alpha^o = R_0/e_1 \in [0,1]$, it maximizes the startup's payoff over $\alpha \in [0,1]$, VC$_1$ invests at $\alpha^o$, and the investment level there is
--   $$\kappa(\alpha^o e_1, \alpha^o e_2, R_0) = R_0 .$$
--
--   This is the benchmark against which the paper measures the effect of crowdfunding: Proposition 6 compares the investment level with crowdfunding to the level $R_0$ (or $0$) established here.
--
--   **Formalization Note** "Optimal" is stated as a global maximizer over $[0,1]$. The hypothesis $0 \le R_f$ (revenue is nonnegative) is not written in the paper and is added to every statement of the mission; with $R_f < 0$ several results of the paper fail.
-- source:
--   Hu, Jin & Keppo, The Crowdfunding Effects on Venture Capital Investment, SSRN author manuscript (abstract 3512638, 2024-03-15; Management Science DOI 10.1287/mnsc.2022.00994), PDF p. 12, Proposition 1 (and the display max_α I{R0/e1≤α≤1}(1 − α)ea); proof Online Appendix D, PDF p. 44 (OA p. 17)

import Mathlib
import Definitions.Def_CrowdfundVC_Effects_Model

namespace CrowdfundVC.Effects

/-- Proposition 1 (Hu, Jin & Keppo, p. 12). Without crowdfunding: if `e1 < R0`, VC1 invests at no
equity share `α ∈ [0, 1]` and the investment level is `0`; if `e1 ≥ R0`, the share `αᵒ = R0/e1` lies in
`[0, 1]`, maximizes the startup's payoff over `[0, 1]`, and VC1 invests `R0` at it. -/
theorem proposition1 (P : Params)
    (hRf0 : 0 ≤ P.Rf) (hRfR0 : P.Rf < P.R0) (hR0Rs : P.R0 < P.Rs) (hK0 : 0 < P.K)
    (hKR0 : P.K < P.R0) (hρ0 : 0 ≤ P.ρ) (hρ1 : P.ρ ≤ 1) (hβ0 : 0 ≤ P.β) (hβ1 : P.β ≤ 1)
    (hp2 : 0 ≤ P.p2) (hp12 : P.p2 ≤ P.p1) (hp1 : P.p1 ≤ 1) (hpa0 : 0 ≤ P.pa) (hpa1 : P.pa ≤ 1)
    (hI : P.R0 ≤ e1S P) :
    (e1 P < P.R0 → ∀ α : ℝ, 0 ≤ α → α ≤ 1 → ¬ investsNoCF P α ∧ invLevelNoCF P α = 0) ∧
    (P.R0 ≤ e1 P →
      (0 ≤ P.R0 / e1 P ∧ P.R0 / e1 P ≤ 1) ∧
      (∀ α : ℝ, 0 ≤ α → α ≤ 1 → payoffNoCF P α ≤ payoffNoCF P (P.R0 / e1 P)) ∧
      investsNoCF P (P.R0 / e1 P) ∧ invLevelNoCF P (P.R0 / e1 P) = P.R0) := by sorry

end CrowdfundVC.Effects
