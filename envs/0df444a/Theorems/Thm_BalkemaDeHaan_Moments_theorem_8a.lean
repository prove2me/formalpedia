-- Prove2me | Theorems.Thm_BalkemaDeHaan_Moments_theorem_8a
-- name    : BalkemaDeHaan.Moments.theorem_8a
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T17:11:02.051+00:00
-- url     : https://prove2.me/theorems/4fb35c49-3e40-48b8-b9bf-43d93756b677
-- title:
--   Theorem 8(a), corrected — $F\in D_r(\Gamma_\alpha)$ iff $\int_0^\infty y^\xi dF<\infty$ and $E((X/t)^\xi\mid X>t)\to(1-\xi/\alpha)^{-1}$
-- statement:
--   Let $X$ be a real random variable with distribution function $F$ such that $F(x) < 1$ for all real $x$, and let $0 < \xi < \alpha$. Write $\Gamma_\alpha(x) = 1 - (1+x)^{-\alpha}$ for $x \ge 0$ and $\Gamma_\alpha(x) = 0$ for $x < 0$. Then
--
--   $$
--   \lim_{t\to\infty} P\Big\{\frac{X}{t} \le x \,\Big|\, X > t\Big\} = \Gamma_\alpha(x-1) \quad\text{for all } x > 0
--   $$
--
--   if and only if $\int_0^\infty y^\xi\, dF(y)$ is finite and
--
--   $$
--   \lim_{t\to\infty} E\Big(\Big(\frac{X}{t}\Big)^{\xi}\,\Big|\, X > t\Big) = \Big(1 - \frac{\xi}{\alpha}\Big)^{-1}.
--   $$
--
--   The left-hand condition says that $F$ lies in the domain of residual life time attraction of $\Gamma_\alpha$: given survival to a great age $t$, the age at death measured in units of $t$ is asymptotically Pareto with index $\alpha$. The theorem replaces this distributional condition by the convergence of a single conditional moment of any order $\xi \in (0,\alpha)$.
--
--   **Formalization Note** The paper states the right-hand side as "$\int_0^\infty y^\xi dF(y)$ is finite and $c = \lim_{t\to\infty} E((X/t)^\xi \mid X > t)$ exists and is finite. Then $c = (1-\xi/\alpha)^{-1}$." The "if" direction of that wording is false: a Pareto tail $1-F(x) = x^{-\beta}$ ($x\ge1$), $\beta>\xi$, $\beta\ne\alpha$, has a finite moment and constant conditional moment $(1-\xi/\beta)^{-1}$ but limit law $\Gamma_\beta(x-1)$. The formal statement puts the value $(1-\xi/\alpha)^{-1}$ of $c$ into the right-hand side; the "only if" direction, including "Then $c = (1-\xi/\alpha)^{-1}$", is exactly the page's. The left-hand side is the explicit limit form the paper gives after "i.e.", stated for all $x > 0$ as printed. Finiteness of the moment is integrability of $y\mapsto y^\xi$ on $(0,\infty)$ for the law of $X$.
-- source:
--   Balkema, de Haan, Residual Life Time at Great Age, Ann. Probab. 2 (1974), p. 803 (PDF p. 12), Theorem 8(a) (corrected)

import Mathlib
import Definitions.Def_BalkemaDeHaan_ParetoBounds_GammaLaw
import Definitions.Def_BalkemaDeHaan_Moments_ResidualLife

open MeasureTheory Filter Topology

namespace BalkemaDeHaan.Moments

/-- Theorem 8(a), p. 803, **corrected**: suppose `F(x) < 1` for all real `x` and `0 < ξ < α`. Then
`lim_{t→∞} P{X/t ≤ x | X > t} = Γ_α(x − 1)` for all `x > 0` if and only if `∫_0^∞ y^ξ dF(y)` is
finite and `lim_{t→∞} E((X/t)^ξ | X > t) = (1 − ξ/α)^{−1}`. (The page's right-hand side asks only that
the limit exist and be finite, which does not determine `α`; see the Formalization Note.) -/
theorem theorem_8a (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hD₀ : ∀ x : ℝ, 0 < μ (Set.Ioi x))
    (α ξ : ℝ) (hξ : 0 < ξ) (hξα : ξ < α) :
    (∀ x : ℝ, 0 < x →
      Tendsto (fun t : ℝ => scaledResidualCDF μ t x) atTop (𝓝 (BalkemaDeHaan.ParetoBounds.GammaLaw α (x - 1)))) ↔
    (IntegrableOn (fun y : ℝ => y ^ ξ) (Set.Ioi 0) μ ∧
      Tendsto (fun t : ℝ => condMoment μ ξ t) atTop (𝓝 (1 - ξ / α)⁻¹)) := by sorry

end BalkemaDeHaan.Moments
