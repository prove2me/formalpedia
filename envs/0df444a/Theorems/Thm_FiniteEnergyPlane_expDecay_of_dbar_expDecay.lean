-- Prove2me | Theorems.Thm_FiniteEnergyPlane_expDecay_of_dbar_expDecay
-- name    : FiniteEnergyPlane.expDecay_of_dbar_expDecay
-- status  : Open
-- author  : @Mazecto
-- created : 2026-10-29T21:31:59.213069+00:00
-- url     : https://prove2.me/theorems/3f8c98e0-d1b5-493d-8801-689aca09266a
-- title:
--   Exponential decay on a half-cylinder from an exponentially small Cauchy–Riemann defect
-- statement:
--   Let $f,g:\mathbb{R}^2\to\mathbb{R}$ be $1$-periodic in $t$ for $s\ge s_0$ and tend to $0$ in $C^\infty$, uniformly in $t$, as $s\to+\infty$. Suppose that for some $\delta>0$ and $C$, $$|\partial_sf-\partial_tg|+|\partial_tf+\partial_sg|\le Ce^{-\delta s}\qquad(s\ge s_0).$$Then $f$ and $g$ decay exponentially: there are $\delta'>0$, $C'$ and $s_1$ with $|f(s,t)|,|g(s,t)|\le C'e^{-\delta' s}$ for all $s\ge s_1$ and all $t$.
--
--   In other words, a function $f+ig$ on a half-cylinder that tends to $0$ and is holomorphic up to an exponentially small error decays exponentially. This is the scalar statement behind the exponential convergence of the directions of an end tangent to a trivial cylinder.
--
--   **Formalization Note** $C^\infty$ convergence is `TendstoZeroCInfty` (smooth on some $(s_0,\infty)\times\mathbb{R}$, every derivative tends to $0$ uniformly in $t$); partial derivatives are `fderiv ℝ _ (s, t) (1, 0)` and `fderiv ℝ _ (s, t) (0, 1)`.
-- source:
--   Used for C. Wendl, Lectures on Symplectic Field Theory (2026 notes), Proposition 6.7.1, and U. Hryniewicz, J. Symplectic Geom. 12 (2014), Theorem 2.10

import Definitions.Def_FiniteEnergyPlane_Asymptotics

namespace FiniteEnergyPlane

open MeasureTheory Metric Filter Topology
open scoped ContDiff ENNReal Real

/-- Let `f, g : ℝ × ℝ → ℝ` be `1`-periodic in `t` for `s ≥ s₀` and tend to `0` in `C^∞` as
`s → +∞`. If the Cauchy–Riemann defect of `f + i g` decays exponentially,
`|∂ₛf - ∂ₜg| + |∂ₜf + ∂ₛg| ≤ C e^{-δs}` with `δ > 0`, then `f` and `g` decay exponentially:
`|f|, |g| ≤ C' e^{-δ' s}` for some `δ' > 0`. -/
theorem expDecay_of_dbar_expDecay (f g : ℝ × ℝ → ℝ) (hf : TendstoZeroCInfty f)
    (hg : TendstoZeroCInfty g) (δ C s₀ : ℝ) (hδ : 0 < δ)
    (hper : ∀ s ≥ s₀, ∀ t : ℝ, f (s, t + 1) = f (s, t) ∧ g (s, t + 1) = g (s, t))
    (hdbar : ∀ s ≥ s₀, ∀ t : ℝ,
      |fderiv ℝ f (s, t) (1, 0) - fderiv ℝ g (s, t) (0, 1)| +
        |fderiv ℝ f (s, t) (0, 1) + fderiv ℝ g (s, t) (1, 0)| ≤ C * Real.exp (-(δ * s))) :
    ∃ δ' > 0, ∃ C' s₁ : ℝ, ∀ s ≥ s₁, ∀ t : ℝ,
      |f (s, t)| ≤ C' * Real.exp (-(δ' * s)) ∧ |g (s, t)| ≤ C' * Real.exp (-(δ' * s)) := by
  sorry

end FiniteEnergyPlane
