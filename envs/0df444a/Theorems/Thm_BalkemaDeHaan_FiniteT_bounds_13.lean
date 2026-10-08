-- Prove2me | Theorems.Thm_BalkemaDeHaan_FiniteT_bounds_13
-- name    : BalkemaDeHaan.FiniteT.bounds_13
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T17:09:17.820581+00:00
-- url     : https://prove2.me/theorems/f7592bce-629a-4258-8680-14d23f250e53
-- title:
--   (13), proof of Theorem 7 — 1 + c₁x ≤ a(t + xa(t))/a(t) ≤ 1 + c₂x
-- statement:
--   Let $X$ have distribution function $F$ with a positive, differentiable density $F'$ for $t \ge t_0$, and let $a(t) = (1 - F(t))/F'(t)$. Suppose $a$ has derivative $a'(t)$ on $[t_0, \infty)$ and $c_1 \le a'(t) \le c_2$ for $t \ge t_0$. Then for every $t \ge t_0$ and $x \ge 0$,
--   $$
--   c_1 x\, a(t) \le a(t + x a(t)) - a(t) \le c_2 x\, a(t),
--   $$
--   or equivalently
--   $$
--   1 + c_1 x \le \frac{a(t + x a(t))}{a(t)} \le 1 + c_2 x .
--   $$
--   These bounds on the growth of the norming function are what Theorem 7 converts into bounds on the residual life distribution.
--
--   **Formalization Note** The derivative of $a$ is a named function $a'$ with `HasDerivWithinAt` on $[t_0,\infty)$; it is the derivative the density hypotheses already provide. Both displays of the page are stated, as a conjunction.
-- source:
--   Balkema, de Haan, Residual Life Time at Great Age, Ann. Probab. 2 (1974), p. 802 (PDF 11), proof of Theorem 7, (13)

import Mathlib
import Definitions.Def_BalkemaDeHaan_FiniteT_Pi0
import Definitions.Def_BalkemaDeHaan_FiniteT_ResidualLife

open MeasureTheory ProbabilityTheory

namespace BalkemaDeHaan.FiniteT

/-- The bounds (13), proof of Theorem 7, p. 802: if `c₁ ≤ a′ ≤ c₂` on `[t₀, ∞)` for
`a(t) = (1 - F(t))/F′(t)`, then for `t ≥ t₀` and `x ≥ 0`,
`c₁ x a(t) ≤ a(t + x a(t)) - a(t) ≤ c₂ x a(t)` and `1 + c₁ x ≤ a(t + x a(t))/a(t) ≤ 1 + c₂ x`. -/
theorem bounds_13 (μ : Measure ℝ) [IsProbabilityMeasure μ] (t₀ : ℝ) (f f' a' : ℝ → ℝ)
    (hdens : HasPosDiffDensity μ t₀ f f')
    (ha' : ∀ t ≥ t₀, HasDerivWithinAt (normA μ f) (a' t) (Set.Ici t₀) t)
    (c₁ c₂ : ℝ) (hc : ∀ t ≥ t₀, c₁ ≤ a' t ∧ a' t ≤ c₂) :
    ∀ t ≥ t₀, ∀ x : ℝ, 0 ≤ x →
      (c₁ * x * normA μ f t ≤ normA μ f (t + x * normA μ f t) - normA μ f t ∧
        normA μ f (t + x * normA μ f t) - normA μ f t ≤ c₂ * x * normA μ f t) ∧
      (1 + c₁ * x ≤ normA μ f (t + x * normA μ f t) / normA μ f t ∧
        normA μ f (t + x * normA μ f t) / normA μ f t ≤ 1 + c₂ * x) := by sorry

end BalkemaDeHaan.FiniteT
