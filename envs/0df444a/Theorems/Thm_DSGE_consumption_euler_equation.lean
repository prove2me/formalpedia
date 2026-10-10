-- Prove2me | Theorems.Thm_DSGE_consumption_euler_equation
-- name    : DSGE.consumption_euler_equation
-- status  : Open
-- author  : @Lucas
-- created : 2026-10-09T21:28:13.000263+00:00
-- url     : https://prove2.me/theorems/8e59132f-f0a8-4863-9c2c-2b3ef825c5f7
-- title:
--   Consumption Euler equation (two-period problem)
-- statement:
--   Consider a consumer with period utility $u : \mathbb R \to \mathbb R$, discount factor $\beta > 0$, real interest rate $r$ with $1 + r > 0$, and wealth $w$. Consuming $c_0$ today leaves $w - c_0$ to be saved, which pays $c_1 = (1+r)(w - c_0)$ tomorrow; lifetime utility is $U(c_0) = u(c_0) + \beta\, u\big((1+r)(w-c_0)\big)$. If $c_0 \in (0, w)$ maximises $U$ over $(0, w)$, and $u$ is differentiable at $c_0$ and at $c_1 = (1+r)(w-c_0)$, then
--   $$
--   u'(c_0) = \beta\,(1+r)\,u'(c_1).
--   $$
--
--   This is the consumption Euler equation that the source describes in words: "our marginal utility from consumption today must equal our marginal utility from consumption in the future, with a weighting parameter that refers to the valuation that we place on the future relative to today." Its log-linearisation is the demand block (dynamic IS curve) of the New Keynesian model.
--
--   **Formalization Note.** The hypotheses $\beta > 0$ and $1 + r > 0$ are the model's standing conventions; the first-order condition itself does not depend on them.
-- source:
--   Wikipedia, "Dynamic stochastic general equilibrium" (uploaded PDF), section "DSGE modeling — Structure" (simplified demand / supply / monetary-policy model) and section "Criticism" (consumption Euler equation paragraph); https://en.wikipedia.org/wiki/Dynamic_stochastic_general_equilibrium (Criticism section: "the central equation for consumption ... marginal utility from consumption today must equal our marginal utility from consumption in the future, with a weighting parameter")

import Mathlib

namespace DSGE
theorem consumption_euler_equation (u : ℝ → ℝ) (β r w c₀ : ℝ)
    (hβ : 0 < β) (hr : 0 < 1 + r) (hc₀ : c₀ ∈ Set.Ioo 0 w)
    (hmax : ∀ c ∈ Set.Ioo 0 w,
      u c + β * u ((1 + r) * (w - c)) ≤ u c₀ + β * u ((1 + r) * (w - c₀)))
    (hu₀ : DifferentiableAt ℝ u c₀) (hu₁ : DifferentiableAt ℝ u ((1 + r) * (w - c₀))) :
    deriv u c₀ = β * (1 + r) * deriv u ((1 + r) * (w - c₀)) := by sorry
end DSGE
