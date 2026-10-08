-- Prove2me | Theorems.Thm_BalkemaDeHaan_FiniteT_corollary_theorem_7
-- name    : BalkemaDeHaan.FiniteT.corollary_theorem_7
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T17:11:57.751004+00:00
-- url     : https://prove2.me/theorems/6355e510-4ff4-476f-b916-abd9d7e3f48e
-- title:
--   Corollary to Theorem 7 — |c − a′(t)| ≤ ε on [t₀, ∞) gives |Π_{0,c}(x) − P{(X − t)/a(t) ≤ x | X > t}| ≤ ε
-- statement:
--   Let $F$ be a distribution function which has a positive, differentiable density $F'$ for $t \ge t_0$, let $X$ have distribution $F$, and let $a(t) = (1 - F(t))/F'(t)$. If $c \ge 0$ and $\varepsilon \ge 0$ satisfy
--   $$
--   \left| c - \frac{d}{dt}\left(\frac{1 - F(t)}{F'(t)}\right)\right| \le \varepsilon \qquad (t \ge t_0),
--   $$
--   then
--   $$
--   \left| \Pi_{0,c}(x) - P\left\{\frac{X - t}{a(t)} \le x \,\middle|\, X > t\right\}\right| \le \varepsilon
--   $$
--   for all real $x$ and all $t \ge t_0$.
--
--   This is an explicit, non-asymptotic version of von Mises' sufficient condition: if the derivative of $(1-F)/F'$ is close to $c$ from age $t_0$ on, the normed residual life is uniformly close to the generalized Pareto (or exponential, $c = 0$) law $\Pi_{0,c}$ at every age $t \ge t_0$.
--
--   **Formalization Note** The derivative of $a$ is a named function $a'$ with `HasDerivWithinAt` on $[t_0,\infty)$; $F$ is `cdf μ` for a probability measure `μ`, and the density hypothesis is taken relative to $[t_0, \infty)$. $P\{(X-t)/a(t) \le x \mid X > t\}$ is $F_t(x\,a(t))$. $\Pi_{0,c}$ for $c < 0$ (needed for $c - \varepsilon$) is completed by $1$ beyond $|c|^{-1}$.
-- source:
--   Balkema, de Haan, Residual Life Time at Great Age, Ann. Probab. 2 (1974), p. 802 (PDF 11), Corollary to Theorem 7

import Mathlib
import Definitions.Def_BalkemaDeHaan_FiniteT_Pi0
import Definitions.Def_BalkemaDeHaan_FiniteT_ResidualLife

open MeasureTheory ProbabilityTheory

namespace BalkemaDeHaan.FiniteT

/-- Corollary to Theorem 7, p. 802: if `c ≥ 0`, `ε ≥ 0` and
`|c - (d/dt)((1 - F(t))/F′(t))| ≤ ε` for `t ≥ t₀`, then
`|Π_{0,c}(x) - P{(X - t)/a(t) ≤ x | X > t}| ≤ ε` for all `x` and all `t ≥ t₀`. -/
theorem corollary_theorem_7 (μ : Measure ℝ) [IsProbabilityMeasure μ] (t₀ : ℝ) (f f' a' : ℝ → ℝ)
    (hdens : HasPosDiffDensity μ t₀ f f')
    (ha' : ∀ t ≥ t₀, HasDerivWithinAt (normA μ f) (a' t) (Set.Ici t₀) t)
    (c ε : ℝ) (hc : 0 ≤ c) (hε : 0 ≤ ε) (hclose : ∀ t ≥ t₀, |c - a' t| ≤ ε) :
    ∀ t ≥ t₀, ∀ x : ℝ, |pi0 c x - BalkemaDeHaan.ParetoBounds.residualLife μ t (x * normA μ f t)| ≤ ε := by sorry

end BalkemaDeHaan.FiniteT
