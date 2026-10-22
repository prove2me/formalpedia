-- Prove2me | Theorems.Thm_AdBlockers_Allow_case_1_ads_ads
-- name    : AdBlockers.Allow.case_1_ads_ads
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-18T22:16:24.60491+00:00
-- url     : https://prove2.me/theorems/ef48888f-05fc-47c3-9be1-68f7cf25a6a3
-- title:
--   Proof of Proposition 1, case 1 (corrected) — a symmetric (Ads, Ads) equilibrium has a = (λ+µ)/(βλ+γµ) and profit (λ+µ)²/(2(βλ+γµ))
-- statement:
--   Let $\lambda, \mu, \beta, \gamma > 0$ and consider the benchmark world without ad blockers, in which both platforms use the Ads plan (every user sees ads; non-adblock users have ad sensitivity $\beta$, the other segment $\gamma$). If $(a, a)$ is a symmetric stage-2 equilibrium of this subgame, then
--   $$
--   a = \frac{\lambda + \mu}{\beta\lambda + \gamma\mu}, \qquad r_1 = r_2 = \frac{(\lambda + \mu)^2}{2(\beta\lambda + \gamma\mu)} .
--   $$
--
--   This is the (Ads, Ads) entry of the benchmark payoff table (Table 1), used in Proposition 1 to compare the (Allow, Allow) revenue with the world without ad blockers.
--
--   **Formalization Note** The paper also asserts that this point *is* an equilibrium; that is false when $\gamma/\beta$ is large (at $(\lambda,\mu,\beta,\gamma) = (1, 1/2, 1/10, 2)$ a platform gains by raising its intensity and serving only the $\lambda$-segment). The statement is therefore posed as a necessary condition on symmetric equilibria.
-- source:
--   Despotakis, Ravi & Srinivasan, The Beneficial Effects of Ad Blockers, SSRN 3083119 (version of Nov. 28, 2017), p. 40, proof of Proposition 1 (Appendix A.1), case 1 (corrected: necessity only); Table 1, p. 17

import Mathlib
import Definitions.Def_AdBlockers_Allow_Model

namespace AdBlockers.Allow

/-- Proof of Proposition 1 (Appendix A.1), case 1, p. 40 (benchmark, both platforms use Ads),
posed as a necessary condition: every symmetric stage-2 equilibrium `(a, a)` of the (Ads, Ads)
subgame has `a = (λ + µ)/(βλ + γµ)`, and each platform then earns `(λ + µ)²/(2(βλ + γµ))`. -/
theorem case_1_ads_ads (lam μ β γ : ℝ) (hlam : 0 < lam) (hμ : 0 < μ) (hβ : 0 < β) (hγ : 0 < γ)
    (a : ℝ) (ha : IsStage2NE lam μ β γ BenchPlan.ads.toPlan BenchPlan.ads.toPlan a a) :
    a = (lam + μ) / (β * lam + γ * μ) ∧
      rev₁ lam μ β γ BenchPlan.ads.toPlan BenchPlan.ads.toPlan a a =
        (lam + μ) ^ 2 / (2 * (β * lam + γ * μ)) ∧
      rev₂ lam μ β γ BenchPlan.ads.toPlan BenchPlan.ads.toPlan a a =
        (lam + μ) ^ 2 / (2 * (β * lam + γ * μ)) := by sorry

end AdBlockers.Allow
