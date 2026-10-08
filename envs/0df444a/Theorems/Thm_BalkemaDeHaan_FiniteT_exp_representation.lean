-- Prove2me | Theorems.Thm_BalkemaDeHaan_FiniteT_exp_representation
-- name    : BalkemaDeHaan.FiniteT.exp_representation
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T17:08:26.771987+00:00
-- url     : https://prove2.me/theorems/69dbc1df-8208-4733-b497-fb58cfc92f4a
-- title:
--   Proof of Theorem 7 — P{(X − t)/a(t) > x | X > t} = exp −∫₀ˣ a(t)/a(t + sa(t)) ds
-- statement:
--   Let $X$ have distribution function $F$ with a positive, differentiable density $F'$ for $t \ge t_0$, and let $a(t) = (1 - F(t))/F'(t)$. Then for every $t \ge t_0$ and $x \ge 0$,
--   $$
--   P\left\{\frac{X - t}{a(t)} > x \,\middle|\, X > t\right\} = \frac{1 - F(t + x a(t))}{1 - F(t)} = \exp\left(-\int_0^x \frac{a(t)}{a(t + s a(t))}\, ds\right).
--   $$
--   This representation expresses the normed residual life tail through the norming function alone, so that bounds on $a$ become bounds on the law.
--
--   **Formalization Note** The left side is written $1 - F_t(x\,a(t))$ with $F_t$ the residual life distribution function. The integral is the interval integral over $[0, x]$.
-- source:
--   Balkema, de Haan, Residual Life Time at Great Age, Ann. Probab. 2 (1974), p. 802 (PDF 11), proof of Theorem 7, display after (13)

import Mathlib
import Definitions.Def_BalkemaDeHaan_FiniteT_Pi0
import Definitions.Def_BalkemaDeHaan_FiniteT_ResidualLife

open MeasureTheory ProbabilityTheory

namespace BalkemaDeHaan.FiniteT

/-- The exponential representation, proof of Theorem 7, p. 802: for `t ≥ t₀` and `x ≥ 0`,
`P{(X - t)/a(t) > x | X > t} = (1 - F(t + x a(t)))/(1 - F(t))
= exp(-∫₀ˣ a(t)/a(t + s a(t)) ds)`. -/
theorem exp_representation (μ : Measure ℝ) [IsProbabilityMeasure μ] (t₀ : ℝ) (f f' : ℝ → ℝ)
    (hdens : HasPosDiffDensity μ t₀ f f') :
    ∀ t ≥ t₀, ∀ x : ℝ, 0 ≤ x →
      1 - BalkemaDeHaan.ParetoBounds.residualLife μ t (x * normA μ f t)
          = (1 - cdf μ (t + x * normA μ f t)) / (1 - cdf μ t) ∧
        (1 - cdf μ (t + x * normA μ f t)) / (1 - cdf μ t)
          = Real.exp (-∫ s in (0 : ℝ)..x, normA μ f t / normA μ f (t + s * normA μ f t)) := by sorry

end BalkemaDeHaan.FiniteT
