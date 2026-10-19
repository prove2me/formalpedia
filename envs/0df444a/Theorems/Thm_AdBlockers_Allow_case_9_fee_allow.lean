-- Prove2me | Theorems.Thm_AdBlockers_Allow_case_9_fee_allow
-- name    : AdBlockers.Allow.case_9_fee_allow
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-18T22:16:35.147799+00:00
-- url     : https://prove2.me/theorems/9596df03-8619-4e97-ba26-887cc878f38a
-- title:
--   Proof of Proposition 1, case 9 — (Fee, Allow): p₁ = (3λ+2µ)/(3λ+4µ), a₂ = 3(λ+µ)/(β(3λ+4µ)) is a stage-2 equilibrium
-- statement:
--   Let $\lambda, \mu, \beta > 0$ (and $\gamma$ arbitrary) and suppose platform 1 charges a Fee while platform 2 Allows ad blockers. Then the fee and ad intensity
--   $$
--   p_1 = \frac{3\lambda + 2\mu}{3\lambda + 4\mu}, \qquad a_2 = \frac{3(\lambda + \mu)}{\beta(3\lambda + 4\mu)}
--   $$
--   form a stage-2 equilibrium, with revenues
--   $$
--   r_1 = \frac{(\lambda + \mu)(3\lambda + 2\mu)^2}{2(3\lambda + 4\mu)^2}, \qquad r_2 = \frac{9\lambda(\lambda + \mu)^2}{2\beta(3\lambda + 4\mu)^2}.
--   $$
--
--   This is what Proposition 1 needs from case 9: the revenue of a platform that deviates from (Allow, Allow) to Fee.
-- source:
--   Despotakis, Ravi & Srinivasan, The Beneficial Effects of Ad Blockers, SSRN 3083119 (version of Nov. 28, 2017), p. 43, proof of Proposition 1 (Appendix A.1), case 9 (decision values from case 7, same page)

import Mathlib
import Definitions.Def_AdBlockers_Allow_Model

namespace AdBlockers.Allow

/-- Proof of Proposition 1 (Appendix A.1), case 9, p. 43, with the decision values of case 7
(platform 1 charges a Fee, platform 2 Allows ad blockers): the fee `p₁ = (3λ + 2µ)/(3λ + 4µ)` and
the ad intensity `a₂ = 3(λ + µ)/(β(3λ + 4µ))` form a stage-2 equilibrium of the (Fee, Allow)
subgame, with revenues `(λ + µ)(3λ + 2µ)²/(2(3λ + 4µ)²)` and `9λ(λ + µ)²/(2β(3λ + 4µ)²)`. -/
theorem case_9_fee_allow (lam μ β γ : ℝ) (hlam : 0 < lam) (hμ : 0 < μ) (hβ : 0 < β) :
    IsStage2NE lam μ β γ .fee .allow ((3 * lam + 2 * μ) / (3 * lam + 4 * μ))
        (3 * (lam + μ) / (β * (3 * lam + 4 * μ))) ∧
      rev₁ lam μ β γ .fee .allow ((3 * lam + 2 * μ) / (3 * lam + 4 * μ))
          (3 * (lam + μ) / (β * (3 * lam + 4 * μ))) =
        (lam + μ) * (3 * lam + 2 * μ) ^ 2 / (2 * (3 * lam + 4 * μ) ^ 2) ∧
      rev₂ lam μ β γ .fee .allow ((3 * lam + 2 * μ) / (3 * lam + 4 * μ))
          (3 * (lam + μ) / (β * (3 * lam + 4 * μ))) =
        9 * lam * (lam + μ) ^ 2 / (2 * β * (3 * lam + 4 * μ) ^ 2) := by sorry

end AdBlockers.Allow
