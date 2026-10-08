-- Prove2me | Theorems.Thm_BalkemaDeHaan_Moments_theorem_8a_if
-- name    : BalkemaDeHaan.Moments.theorem_8a_if
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T17:10:58.346622+00:00
-- url     : https://prove2.me/theorems/af616775-0bdd-497e-95c4-a8782e012c78
-- title:
--   Theorem 8(a), p. 803 (if, corrected) — $E((X/t)^\xi\mid X>t)\to(1-\xi/\alpha)^{-1}$ with a finite moment gives $F\in D_r(\Gamma_\alpha)$
-- statement:
--   Let $X$ be a real random variable with distribution function $F$ such that $F(x) < 1$ for all real $x$, and let $0 < \xi < \alpha$. Suppose that $\int_0^\infty y^\xi\, dF(y)$ is finite and
--
--   $$
--   \lim_{t\to\infty} E\Big(\Big(\frac{X}{t}\Big)^{\xi}\,\Big|\, X > t\Big) = \Big(1 - \frac{\xi}{\alpha}\Big)^{-1}.
--   $$
--
--   Then $\lim_{t\to\infty} P\{X/t \le x \mid X > t\} = \Gamma_\alpha(x-1)$ for every $x > 0$.
--
--   This is the sufficiency half of the moment characterization: convergence of a single conditional moment of order $\xi$ to the value $(1 - \xi/\alpha)^{-1}$ already forces the scaled residual life times to converge to the Pareto law with index $\alpha$.
--
--   **Formalization Note** The paper's sufficiency condition is only that $\int_0^\infty y^\xi dF(y)$ be finite and that the limit $c$ exist and be finite. As printed this is false: for the Pareto tail $1 - F(x) = x^{-\beta}$ ($x \ge 1$) with $\beta > \xi$, $\beta \ne \alpha$, the moment is finite and $E((X/t)^\xi \mid X > t) = (1-\xi/\beta)^{-1}$ for all $t \ge 1$, yet the limit law is $\Gamma_\beta(x-1) \ne \Gamma_\alpha(x-1)$. The statement here requires the limit to be $(1 - \xi/\alpha)^{-1}$, the value the paper itself identifies in "Then $c = (1-\xi/\alpha)^{-1}$".
-- source:
--   Balkema, de Haan, Residual Life Time at Great Age, Ann. Probab. 2 (1974), p. 803 (PDF p. 12), Theorem 8(a), "if" direction (corrected: c = (1 − ξ/α)^{−1} assumed)

import Mathlib
import Definitions.Def_BalkemaDeHaan_ParetoBounds_GammaLaw
import Definitions.Def_BalkemaDeHaan_Moments_ResidualLife

open MeasureTheory Filter Topology

namespace BalkemaDeHaan.Moments

/-- Theorem 8(a), p. 803, the "if" half, **corrected**: if `F(x) < 1` for all `x`, `0 < ξ < α`,
`∫_0^∞ y^ξ dF(y)` is finite and `E((X/t)^ξ | X > t) → (1 − ξ/α)^{−1}` as `t → ∞`, then
`P{X/t ≤ x | X > t} → Γ_α(x − 1)` for all `x > 0`. The page asks only that the limit `c` exist and be
finite; that is false (a Pareto BalkemaDeHaan.LimitTypes.tail `x^{−β}`, `β > ξ`, `β ≠ α`, gives `c = (1 − ξ/β)^{−1}` and the
limit law `Γ_β(x − 1)`), so the limit value `(1 − ξ/α)^{−1}` is part of the hypothesis. -/
theorem theorem_8a_if (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hD₀ : ∀ x : ℝ, 0 < μ (Set.Ioi x))
    (α ξ : ℝ) (hξ : 0 < ξ) (hξα : ξ < α)
    (hmom : IntegrableOn (fun y : ℝ => y ^ ξ) (Set.Ioi 0) μ)
    (hc : Tendsto (fun t : ℝ => condMoment μ ξ t) atTop (𝓝 (1 - ξ / α)⁻¹)) :
    ∀ x : ℝ, 0 < x →
      Tendsto (fun t : ℝ => scaledResidualCDF μ t x) atTop (𝓝 (BalkemaDeHaan.ParetoBounds.GammaLaw α (x - 1))) := by sorry

end BalkemaDeHaan.Moments
