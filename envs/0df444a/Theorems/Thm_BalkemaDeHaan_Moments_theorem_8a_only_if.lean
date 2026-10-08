-- Prove2me | Theorems.Thm_BalkemaDeHaan_Moments_theorem_8a_only_if
-- name    : BalkemaDeHaan.Moments.theorem_8a_only_if
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T17:10:43.113989+00:00
-- url     : https://prove2.me/theorems/12473f3f-4be1-47df-bcc4-1aacccfad933
-- title:
--   Theorem 8(a), p. 803 (only if) — $F\in D_r(\Gamma_\alpha)$ gives a finite $\xi$-th moment and $E((X/t)^\xi\mid X>t)\to(1-\xi/\alpha)^{-1}$
-- statement:
--   Let $X$ be a real random variable with distribution function $F$ such that $F(x) < 1$ for all real $x$, and let $0 < \xi < \alpha$. Suppose that
--
--   $$
--   \lim_{t\to\infty} P\Big\{\frac{X}{t} \le x \,\Big|\, X > t\Big\} = \Gamma_\alpha(x-1) \qquad \text{for all } x > 0 ,
--   $$
--
--   where $\Gamma_\alpha(x) = 1 - (1+x)^{-\alpha}$ for $x \ge 0$ and $0$ for $x < 0$. Then $\int_0^\infty y^\xi\, dF(y)$ is finite and
--
--   $$
--   \lim_{t\to\infty} E\Big(\Big(\frac{X}{t}\Big)^{\xi}\,\Big|\, X > t\Big) = \Big(1 - \frac{\xi}{\alpha}\Big)^{-1}.
--   $$
--
--   This is the necessity half of the moment characterization of the domain of residual life time attraction of $\Gamma_\alpha$: weak convergence of the scaled residual life times forces convergence of every moment of order below $\alpha$, to the corresponding moment of the Pareto limit law.
--
--   **Formalization Note** "$\int_0^\infty y^\xi dF(y)$ is finite" is integrability of $y \mapsto y^\xi$ on $(0,\infty)$ for the law of $X$; it is part of the conclusion. The limit is along real $t \to \infty$. The conditional distribution function and conditional moment are those of the definition `BalkemaDeHaan.Moments.ResidualLife`.
-- source:
--   Balkema, de Haan, Residual Life Time at Great Age, Ann. Probab. 2 (1974), p. 803 (PDF p. 12), Theorem 8(a), "only if" direction with "Then c = (1 − ξ/α)^{−1}"

import Mathlib
import Definitions.Def_BalkemaDeHaan_ParetoBounds_GammaLaw
import Definitions.Def_BalkemaDeHaan_Moments_ResidualLife

open MeasureTheory Filter Topology

namespace BalkemaDeHaan.Moments

/-- Theorem 8(a), p. 803, the "only if" half together with "Then c = (1 − ξ/α)^{−1}": if
`F(x) < 1` for all `x`, `0 < ξ < α` and `P{X/t ≤ x | X > t} → Γ_α(x − 1)` as `t → ∞` for all
`x > 0`, then `∫_0^∞ y^ξ dF(y)` is finite and `E((X/t)^ξ | X > t) → (1 − ξ/α)^{−1}`. -/
theorem theorem_8a_only_if (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hD₀ : ∀ x : ℝ, 0 < μ (Set.Ioi x))
    (α ξ : ℝ) (hξ : 0 < ξ) (hξα : ξ < α)
    (hlim : ∀ x : ℝ, 0 < x →
      Tendsto (fun t : ℝ => scaledResidualCDF μ t x) atTop (𝓝 (BalkemaDeHaan.ParetoBounds.GammaLaw α (x - 1)))) :
    IntegrableOn (fun y : ℝ => y ^ ξ) (Set.Ioi 0) μ ∧
    Tendsto (fun t : ℝ => condMoment μ ξ t) atTop (𝓝 (1 - ξ / α)⁻¹) := by sorry

end BalkemaDeHaan.Moments
