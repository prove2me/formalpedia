-- Prove2me | Theorems.Thm_AdBlockers_Allow_proposition_1
-- name    : AdBlockers.Allow.proposition_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-18T22:16:35.885871+00:00
-- url     : https://prove2.me/theorems/885e6537-a437-4522-bae0-790f3c8c7036
-- title:
--   Proposition 1 — both platforms Allowing ad blockers is an equilibrium, and beats the world without ad blockers for low β and high γ/β
-- statement:
--   Consider two platforms competing on a Hotelling line for non-adblock users (mass $\lambda$, ad sensitivity $\beta$) and adblock users (mass $\mu$, ad sensitivity $\gamma$), each choosing a plan Ban, Allow or Fee and then an ad intensity or a fee. Let $\lambda, \mu, \beta, \gamma > 0$.
--
--   1. If
--   $$
--   \beta \le \frac{\lambda(3\lambda + 4\mu)^2}{(\lambda+\mu)(3\lambda+2\mu)^2} \qquad\text{and}\qquad \frac{\lambda + \mu\cdot\gamma/\beta}{(3\lambda + 4\mu\cdot\gamma/\beta)^2} \le \frac{\lambda}{(3\lambda+2\mu)^2},
--   $$
--   then both platforms Allowing ad blockers with ad intensities $a_1 = a_2 = 1/\beta$ is an equilibrium of the two-stage game, and each platform earns $\lambda/(2\beta)$.
--   2. If
--   $$
--   \frac{\gamma}{\beta} \ge 2 + \frac{\mu}{\lambda} \qquad\text{and}\qquad \beta \le \frac{\lambda}{\lambda + \mu},
--   $$
--   then the same holds, and moreover each platform's revenue $\lambda/(2\beta)$ is at least its revenue in every symmetric stage-2 equilibrium of the benchmark subgames (Ads, Ads) and (Fee, Fee) of the world without ad blockers.
--
--   So when $\beta$ is low and $\gamma/\beta$ is high, the presence of ad blockers makes the platforms better off.
--
--   **Formalization Note** "Equilibrium" means: $(1/\beta, 1/\beta)$ is a pure Nash equilibrium of the (Allow, Allow) pricing subgame, and after every unilateral change of plan by either platform there is a stage-2 equilibrium of the resulting subgame in which the deviator earns no more. Market shares are clipped to $[0,1]$ and decision variables range over $[0,\infty)$. The first condition corrects a typo on p. 44 (the paper prints $(3\lambda+2\mu)^2$ in the numerator). The benchmark comparison quantifies over actual stage-2 equilibria; for large $\gamma/\beta$ the (Ads, Ads) subgame may have no symmetric equilibrium, in which case that clause holds vacuously, while the (Fee, Fee) subgame always has one. "Better off" is the paper's weak inequality.
-- source:
--   Despotakis, Ravi & Srinivasan, The Beneficial Effects of Ad Blockers, SSRN 3083119 (version of Nov. 28, 2017), p. 19, Proposition 1; thresholds from its proof, Appendix A.1, p. 44 (first condition corrected)

import Mathlib
import Definitions.Def_AdBlockers_Allow_Model

namespace AdBlockers.Allow

/-- Proposition 1, p. 19 (thresholds from its proof, Appendix A.1, p. 44; the first condition
corrected). Let `λ, µ, β, γ > 0`.

(i) If `β ≤ λ(3λ + 4µ)²/((λ + µ)(3λ + 2µ)²)` and
`(λ + µ·γ/β)/(3λ + 4µ·γ/β)² ≤ λ/(3λ + 2µ)²`, then both platforms Allowing ad blockers with ad
intensities `a₁ = a₂ = 1/β` is an equilibrium, in which each platform earns `λ/(2β)`.

(ii) If `γ/β ≥ 2 + µ/λ` and `β ≤ λ/(λ + µ)`, then the same holds, and each platform's revenue
`λ/(2β)` is at least its revenue in every symmetric stage-2 equilibrium of the benchmark (Ads, Ads)
and (Fee, Fee) subgames of the world without ad blockers. -/
theorem proposition_1 (lam μ β γ : ℝ) (hlam : 0 < lam) (hμ : 0 < μ) (hβ : 0 < β) (hγ : 0 < γ) :
    (β ≤ lam * (3 * lam + 4 * μ) ^ 2 / ((lam + μ) * (3 * lam + 2 * μ) ^ 2) →
      (lam + μ * (γ / β)) / (3 * lam + 4 * μ * (γ / β)) ^ 2 ≤ lam / (3 * lam + 2 * μ) ^ 2 →
      IsEquilibrium lam μ β γ .allow .allow (1 / β) (1 / β) ∧
        rev₁ lam μ β γ .allow .allow (1 / β) (1 / β) = lam / (2 * β) ∧
        rev₂ lam μ β γ .allow .allow (1 / β) (1 / β) = lam / (2 * β)) ∧
    (2 + μ / lam ≤ γ / β → β ≤ lam / (lam + μ) →
      IsEquilibrium lam μ β γ .allow .allow (1 / β) (1 / β) ∧
        rev₁ lam μ β γ .allow .allow (1 / β) (1 / β) = lam / (2 * β) ∧
        rev₂ lam μ β γ .allow .allow (1 / β) (1 / β) = lam / (2 * β) ∧
        (∀ a : ℝ, IsStage2NE lam μ β γ BenchPlan.ads.toPlan BenchPlan.ads.toPlan a a →
          rev₁ lam μ β γ BenchPlan.ads.toPlan BenchPlan.ads.toPlan a a ≤ lam / (2 * β) ∧
          rev₂ lam μ β γ BenchPlan.ads.toPlan BenchPlan.ads.toPlan a a ≤ lam / (2 * β)) ∧
        (∀ p : ℝ, IsStage2NE lam μ β γ BenchPlan.fee.toPlan BenchPlan.fee.toPlan p p →
          rev₁ lam μ β γ BenchPlan.fee.toPlan BenchPlan.fee.toPlan p p ≤ lam / (2 * β) ∧
          rev₂ lam μ β γ BenchPlan.fee.toPlan BenchPlan.fee.toPlan p p ≤ lam / (2 * β))) := by sorry

end AdBlockers.Allow
