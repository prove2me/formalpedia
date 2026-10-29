-- Prove2me | Theorems.Thm_FiniteEnergyPlane_halfCyl_eventually_ne_zero
-- name    : FiniteEnergyPlane.halfCyl_eventually_ne_zero
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-10-21T12:42:49.102058+00:00
-- url     : https://prove2.me/theorems/f15a583c-d9a0-4a59-8e3c-ecd666ab428e
-- title:
--   Solutions of linear Cauchy–Riemann equations have no zeros near infinity
-- statement:
--   Let $S:\mathbb{R}^2\to\mathbb{R}^{2n\times2n}$ be $C^\infty$ and $1$-periodic in $t$, and $S_\infty$ a $C^\infty$ $1$-periodic loop of symmetric matrices with $S\to S_\infty$ in $C^\infty$. Let $\zeta$ be a solution of $\partial_s\zeta+J_0\partial_t\zeta+S\zeta=0$ on the half-cylinder, not identically zero on $(0,\infty)\times\mathbb{R}$, with $\|\zeta(s,t)\|\le Ce^{\delta_0s}$ for $s>0$. Then there is $s_0$ with $\zeta(s,t)\neq0$ for all $s\ge s_0$ and all $t$.
--
--   **Formalization Note** No rate of convergence of $S$ and no nondegeneracy of $S_\infty$ is assumed.
-- source:
--   C. Wendl, Lectures on Symplectic Field Theory, lecture notes, Humboldt-Universität zu Berlin (2026 version); earlier version arXiv:1612.01009, Corollary 4.8.3

import Definitions.Def_FiniteEnergyPlane_Asymptotics

namespace FiniteEnergyPlane

open MeasureTheory Metric Filter Topology
open scoped ContDiff ENNReal Real

/-- A solution of `∂ₛζ + J₀ ∂ₜζ + S ζ = 0` on a half-cylinder, with `S(s, t) → S∞(t)` in `C^∞`,
not identically zero and with `‖ζ(s, t)‖ ≤ C e^{δ₀ s}`, has no zeros for `s` large. -/
theorem halfCyl_eventually_ne_zero {n : ℕ} (S : ℝ × ℝ → CauchyRiemannIndex.Mat n)
    (hS : ∀ i j, ContDiff ℝ ∞ (fun p : ℝ × ℝ => S p i j)) (hSper : ∀ s t : ℝ, S (s, t + 1) = S (s, t))
    (Sinf : ℝ → CauchyRiemannIndex.Mat n) (hSinf : CauchyRiemannIndex.IsSymLoop Sinf)
    (hSinf' : ∀ i j, ContDiff ℝ ∞ (fun t => Sinf t i j))
    (hSas : IsCInftyAsymptoticTo S Sinf)
    (ζ : ℝ × ℝ → CauchyRiemannIndex.Vec n) (hζ : IsHalfCylSolution S ζ)
    (hne : ∃ p : ℝ × ℝ, 0 < p.1 ∧ ζ p ≠ 0)
    (C δ₀ : ℝ) (hgrowth : ∀ s > 0, ∀ t : ℝ, ‖ζ (s, t)‖ ≤ C * Real.exp (δ₀ * s)) :
    ∃ s₀ : ℝ, ∀ s ≥ s₀, ∀ t : ℝ, ζ (s, t) ≠ 0 := by
  sorry

end FiniteEnergyPlane
