-- Prove2me | Theorems.Thm_BalkemaDeHaan_FiniteT_theorem_7
-- name    : BalkemaDeHaan.FiniteT.theorem_7
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T17:08:29.724974+00:00
-- url     : https://prove2.me/theorems/ac0b893e-da00-40ad-8ec5-b83958397bd8
-- title:
--   Theorem 7 — c₁ ≤ a′ ≤ c₂ on [t₀, ∞) gives Π_{0,c₂}(x) ≤ P{(X − t)/a(t) ≤ x | X > t} ≤ Π_{0,c₁}(x)
-- statement:
--   Let $F$ be a distribution function which has a positive, differentiable density $F'$ for $t \ge t_0$, let $a(t) = (1 - F(t))/F'(t)$, and let $c_1, c_2$ be real numbers such that
--   $$
--   c_1 \le \frac{d}{dt}\left(\frac{1 - F(t)}{F'(t)}\right) \le c_2 \qquad (t \ge t_0).
--   $$
--   If $X$ is a random variable with distribution $F$, then for $t \ge t_0$ and all real $x$,
--   $$
--   \Pi_{0,c_2}(x) \le P\left\{\frac{X - t}{a(t)} \le x \,\middle|\, X > t\right\} \le \Pi_{0,c_1}(x).
--   $$
--   Here $\Pi_{0,c}$ is the family of limit laws (generalized Pareto for $c > 0$, exponential for $c = 0$, bounded support for $c < 0$). The theorem gives explicit two-sided bounds on the normed residual life distribution at every finite age $t \ge t_0$, not only in the limit $t \to \infty$. Note the orientation: the upper bound $c_2$ on the derivative gives the lower bound on the distribution function.
--
--   **Formalization Note** The derivative of $a$ is a named function $a'$ with `HasDerivWithinAt` on $[t_0,\infty)$. $P\{(X-t)/a(t) \le x \mid X > t\}$ is $F_t(x\,a(t))$. For $c < 0$, $\Pi_{0,c}$ is completed by $1$ beyond $|c|^{-1}$ (see the definition). No sign condition on $c_1, c_2$ is added.
-- source:
--   Balkema, de Haan, Residual Life Time at Great Age, Ann. Probab. 2 (1974), pp. 801–802 (PDF 10–11), Theorem 7

import Mathlib
import Definitions.Def_BalkemaDeHaan_FiniteT_Pi0
import Definitions.Def_BalkemaDeHaan_FiniteT_ResidualLife

open MeasureTheory ProbabilityTheory

namespace BalkemaDeHaan.FiniteT

/-- Theorem 7, pp. 801–802: let `F = cdf μ` have a positive, differentiable density `f` for
`t ≥ t₀`, and let `c₁ ≤ (d/dt)((1 - F(t))/F′(t)) ≤ c₂` for `t ≥ t₀`. Then for `t ≥ t₀`
and all `x`, `Π_{0,c₂}(x) ≤ P{(X - t)/a(t) ≤ x | X > t} ≤ Π_{0,c₁}(x)`, where
`a(t) = (1 - F(t))/F′(t)` and `P{(X - t)/a(t) ≤ x | X > t} = F_t(x a(t))`. -/
theorem theorem_7 (μ : Measure ℝ) [IsProbabilityMeasure μ] (t₀ : ℝ) (f f' a' : ℝ → ℝ)
    (hdens : HasPosDiffDensity μ t₀ f f')
    (ha' : ∀ t ≥ t₀, HasDerivWithinAt (normA μ f) (a' t) (Set.Ici t₀) t)
    (c₁ c₂ : ℝ) (hc : ∀ t ≥ t₀, c₁ ≤ a' t ∧ a' t ≤ c₂) :
    ∀ t ≥ t₀, ∀ x : ℝ,
      pi0 c₂ x ≤ BalkemaDeHaan.ParetoBounds.residualLife μ t (x * normA μ f t) ∧
        BalkemaDeHaan.ParetoBounds.residualLife μ t (x * normA μ f t) ≤ pi0 c₁ x := by sorry

end BalkemaDeHaan.FiniteT
