-- Prove2me | Theorems.Thm_FiniteEnergyPlane_halfCyl_exp_decay
-- name    : FiniteEnergyPlane.halfCyl_exp_decay
-- status  : Open
-- author  : @Mazecto
-- created : 2026-10-21T12:42:15.44749+00:00
-- url     : https://prove2.me/theorems/81087bad-214a-4897-a63f-af059a468d21
-- title:
--   Exponential decay of solutions of linear Cauchy–Riemann equations on a half-cylinder
-- statement:
--   Let $S:\mathbb{R}^2\to\mathbb{R}^{2n\times2n}$ be $C^\infty$ and $1$-periodic in $t$, and $S_\infty$ a $C^\infty$ $1$-periodic loop of symmetric matrices with $S\to S_\infty$ in $C^\infty$ and $-J_0\partial_t-S_\infty$ nondegenerate. If $\zeta$ is a solution of $\partial_s\zeta+J_0\partial_t\zeta+S\zeta=0$ on the half-cylinder with $\zeta\to0$ uniformly, then there are $\delta>0$ and $C$ with $\|\zeta(s,t)\|\le Ce^{-\delta s}$ for all $s\ge1$ and $t$.
--
--   **Formalization Note** $\zeta$ satisfies `IsHalfCylSolution S ζ` ($C^\infty$ on $(0,\infty)\times\mathbb{R}$). Smoothness of $S$ and $S_\infty$ is entrywise.
-- source:
--   C. Wendl, Lectures on Symplectic Field Theory, lecture notes, Humboldt-Universität zu Berlin (2026 version); earlier version arXiv:1612.01009, Theorem 4.6.6

import Definitions.Def_FiniteEnergyPlane_Asymptotics

namespace FiniteEnergyPlane

open MeasureTheory Metric Filter Topology
open scoped ContDiff ENNReal Real

/-- Exponential decay for linear Cauchy–Riemann equations on a half-cylinder: if `S(s, t) → S∞(t)`
in `C^∞`, the asymptotic operator `-J₀ ∂ₜ - S∞` is nondegenerate, and the solution `ζ` of
`∂ₛζ + J₀ ∂ₜζ + S ζ = 0` tends to `0` uniformly, then `ζ` decays exponentially. -/
theorem halfCyl_exp_decay {n : ℕ} (S : ℝ × ℝ → CauchyRiemannIndex.Mat n)
    (hS : ∀ i j, ContDiff ℝ ∞ (fun p : ℝ × ℝ => S p i j)) (hSper : ∀ s t : ℝ, S (s, t + 1) = S (s, t))
    (Sinf : ℝ → CauchyRiemannIndex.Mat n) (hSinf : CauchyRiemannIndex.IsSymLoop Sinf)
    (hSinf' : ∀ i j, ContDiff ℝ ∞ (fun t => Sinf t i j))
    (hSas : IsCInftyAsymptoticTo S Sinf) (hnd : CauchyRiemannIndex.IsNondegenerate Sinf)
    (ζ : ℝ × ℝ → CauchyRiemannIndex.Vec n) (hζ : IsHalfCylSolution S ζ)
    (hζ0 : TendstoZeroUnif ζ) :
    ∃ δ > 0, ∃ C : ℝ, ∀ s ≥ 1, ∀ t : ℝ, ‖ζ (s, t)‖ ≤ C * Real.exp (-(δ * s)) := by
  sorry

end FiniteEnergyPlane
