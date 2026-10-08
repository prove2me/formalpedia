-- Prove2me | Theorems.Thm_BalkemaDeHaan_ParetoBounds_theorem_6
-- name    : BalkemaDeHaan.ParetoBounds.theorem_6
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T08:03:25.402253+00:00
-- url     : https://prove2.me/theorems/047bb7a6-6957-4c64-8f65-00cc6491d6c9
-- title:
--   Theorem 6 — $\alpha_1 \le tF'(t)/(1-F(t)) \le \alpha_2$ for $t \ge t_0$ gives $\Gamma_{\alpha_1}(x) \le P\{(X-t)/t \le x \mid X>t\} \le \Gamma_{\alpha_2}(x)$
-- statement:
--   Let $F$ be a distribution function on $\mathbb R$ which has a positive density $F'$ for $t \ge t_0$, and let $\alpha_1$ and $\alpha_2$ be positive real numbers such that
--
--   $$
--   \alpha_1 \le \frac{t F'(t)}{1 - F(t)} \le \alpha_2 \qquad \text{for } t \ge t_0 .
--   $$
--
--   If $X$ is a random variable with distribution $F$, then for every $t \ge t_0$ and every real $x$,
--
--   $$
--   \Gamma_{\alpha_1}(x) \;\le\; P\Big\{\frac{X - t}{t} \le x \;\Big|\; X > t\Big\} \;\le\; \Gamma_{\alpha_2}(x),
--   $$
--
--   where $\Gamma_\alpha(x) = 1 - (1+x)^{-\alpha}$ for $x \ge 0$ and $\Gamma_\alpha(x) = 0$ for $x < 0$.
--
--   The quantity $tF'(t)/(1 - F(t))$ is the age times the hazard rate. When it equals a constant $\alpha$ the tail is exactly Pareto, $1 - F(t) = C t^{-\alpha}$, and both bounds are equalities. The theorem is a finite-$t$, two-sided version of von Mises' condition $tF'(t)/(1-F(t)) \to \alpha$: bounds on the scaled hazard rate give explicit bounds on the residual life distribution, uniformly for all ages $t \ge t_0$. The smaller constant $\alpha_1$ (heavier tail) gives the lower bound.
--
--   **Formalization Note** $F$ is `cdf μ` for a probability measure $\mu$ (the law of $X$), and the probability is $F_t(xt) = \mu((t, t + xt])/\mu((t, \infty))$. "Positive density $F'$ for $t \ge t_0$" is an explicit function $f$ with $F$ differentiable at every $t \ge t_0$ with derivative $f(t) > 0$, the derivative being taken within $[t_0, \infty)$ (a right derivative at $t_0$, the ordinary derivative for $t > t_0$); this is the weakest reading of the page and admits the Pareto law with $t_0 = 1$, whose $F$ has no two-sided derivative at $1$. No hypothesis is added: $t_0 > 0$ and $F(t) < 1$ for all $t$ are consequences of the stated hypotheses (at $t \le 0$ the ratio is not $\ge \alpha_1 > 0$; a positive derivative on $[t_0,\infty)$ makes $F$ strictly increasing there), so Lean's conventions $t\cdot f(t)/0 = 0$ and $a/0 = 0$ never act at the ages concerned. The conclusion holds for all real $x$, as printed; for $x \le 0$ all three quantities are $0$.
-- source:
--   Balkema, de Haan, Residual Life Time at Great Age, Ann. Probab. 2 (1974), p. 801 (PDF p. 10), §4, Theorem 6

import Mathlib
import Definitions.Def_BalkemaDeHaan_ParetoBounds_ResidualLife
import Definitions.Def_BalkemaDeHaan_ParetoBounds_GammaLaw

open MeasureTheory ProbabilityTheory

namespace BalkemaDeHaan.ParetoBounds

/-- Theorem 6, p. 801 (Balkema–de Haan 1974): if `F = cdf μ` has a positive density `f`
on `[t₀, ∞)` with `α₁ ≤ t f(t)/(1 - F(t)) ≤ α₂` for `t ≥ t₀`, then for every `t ≥ t₀`
and every real `x`,
`Γ_{α₁}(x) ≤ P{(X - t)/t ≤ x | X > t} ≤ Γ_{α₂}(x)`, where
`P{(X - t)/t ≤ x | X > t} = F_t(x t)`. -/
theorem theorem_6 (μ : Measure ℝ) [IsProbabilityMeasure μ] (f : ℝ → ℝ)
    (t₀ α₁ α₂ : ℝ) (hα₁ : 0 < α₁) (hα₂ : 0 < α₂)
    (hdens : ∀ t ≥ t₀, HasDerivWithinAt (cdf μ) (f t) (Set.Ici t₀) t ∧ 0 < f t)
    (hbounds : ∀ t ≥ t₀, α₁ ≤ t * f t / (1 - cdf μ t) ∧ t * f t / (1 - cdf μ t) ≤ α₂) :
    ∀ t ≥ t₀, ∀ x : ℝ,
      GammaLaw α₁ x ≤ residualLife μ t (x * t) ∧ residualLife μ t (x * t) ≤ GammaLaw α₂ x := by sorry

end BalkemaDeHaan.ParetoBounds
