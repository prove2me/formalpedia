-- Prove2me | Theorems.Thm_FiniteEnergyPlane_halfCyl_exists_tendsto_rayleigh
-- name    : FiniteEnergyPlane.halfCyl_exists_tendsto_rayleigh
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-10-28T22:00:29.750911+00:00
-- url     : https://prove2.me/theorems/afef1eb8-c6c2-4fd4-b57d-276fd75db857
-- title:
--   Convergence of the slice Rayleigh quotient of a linear Cauchy–Riemann solution on a half-cylinder
-- statement:
--   Let $S:\mathbb{R}^2\to\mathbb{R}^{2n\times2n}$ be $C^\infty$ and $1$-periodic in $t$. Let $S_\infty$ be a $C^\infty$, $1$-periodic loop of symmetric matrices with $S(s,t)\to S_\infty(t)$ in $C^\infty$ as $s\to\infty$. Let $\zeta$ be a solution of $\partial_s\zeta+J_0\partial_t\zeta+S\zeta=0$ on the half-cylinder $(0,\infty)\times\mathbb{R}/\mathbb{Z}$. Assume $\zeta$ is not identically zero there and satisfies $\|\zeta(s,t)\|\le Ce^{\delta_0s}$ for $s>0$. Put
--   $$F(s)=\int_0^1\|\zeta(s,t)\|^2\,dt,\qquad \alpha(s)=\frac{\langle\zeta(s,\cdot),\partial_s\zeta(s,\cdot)\rangle_{L^2}}{F(s)},\qquad q(s)=\frac{\|\partial_s\zeta(s,\cdot)\|_{L^2}^2}{F(s)}-\alpha(s)^2 .$$
--
--   Then there are $\mu\le\delta_0$ and $s_0>0$ such that $F(s)>0$ for all $s\ge s_0$, $\alpha(s)\to\mu$ as $s\to\infty$, and $\int_s^{s+1}q(x)\,dx\to0$ as $s\to\infty$.
--
--   This is the convergence statement for the slice Rayleigh quotient $\alpha$ in the qualitative asymptotic analysis of such solutions (C. Wendl, *Lectures on Symplectic Field Theory*, 2026 notes, Theorem 4.6.6), here with no rate of convergence of $S$ to $S_\infty$.
--
--   **Formalization Note** $\partial_s\zeta(s,t)$ is `fderiv ℝ ζ (s, t) (1, 0)`, the $L^2$ products are interval integrals over $[0,1]$, and both limits are along `atTop` in $s\in\mathbb{R}$. The hypothesis $S\to S_\infty$ in $C^\infty$ is `IsCInftyAsymptoticTo S Sinf` (entrywise, all derivatives, uniformly in $t$, no rate).
-- source:
--   C. Wendl, Lectures on Symplectic Field Theory, lecture notes, Humboldt-Universität zu Berlin (2026 version); earlier version arXiv:1612.01009, Theorem 4.6.6

import Definitions.Def_FiniteEnergyPlane_Asymptotics

namespace FiniteEnergyPlane

open MeasureTheory Metric Filter Topology
open scoped ContDiff ENNReal Real RealInnerProductSpace

/-- A solution of `∂ₛζ + J₀ ∂ₜζ + S ζ = 0` on a half-cylinder, with `S(s, t) → S∞(t)` in `C^∞`,
not identically zero and with `‖ζ(s, t)‖ ≤ C e^{δ₀ s}`. Put `F(s) = ∫₀¹ ‖ζ(s, t)‖² dt`,
`α(s) = ⟨ζ(s, ·), ∂ₛζ(s, ·)⟩_{L²} / F(s)` and `q(s) = ‖∂ₛζ(s, ·)‖²_{L²} / F(s) - α(s)²`.
Then `F > 0` on some `[s₀, ∞)`, `α(s)` converges to a limit `μ ≤ δ₀` as `s → ∞`, and
`∫ₛ^{s+1} q → 0`. -/
theorem halfCyl_exists_tendsto_rayleigh {n : ℕ} (S : ℝ × ℝ → CauchyRiemannIndex.Mat n)
    (hS : ∀ i j, ContDiff ℝ ∞ (fun p : ℝ × ℝ => S p i j)) (hSper : ∀ s t : ℝ, S (s, t + 1) = S (s, t))
    (Sinf : ℝ → CauchyRiemannIndex.Mat n) (hSinf : CauchyRiemannIndex.IsSymLoop Sinf)
    (hSinf' : ∀ i j, ContDiff ℝ ∞ (fun t => Sinf t i j))
    (hSas : IsCInftyAsymptoticTo S Sinf)
    (ζ : ℝ × ℝ → CauchyRiemannIndex.Vec n) (hζ : IsHalfCylSolution S ζ)
    (hne : ∃ p : ℝ × ℝ, 0 < p.1 ∧ ζ p ≠ 0)
    (C δ₀ : ℝ) (hgrowth : ∀ s > 0, ∀ t : ℝ, ‖ζ (s, t)‖ ≤ C * Real.exp (δ₀ * s)) :
    ∃ μ : ℝ, μ ≤ δ₀ ∧ ∃ s₀ > 0, (∀ s ≥ s₀, 0 < ∫ t in (0:ℝ)..1, ‖ζ (s, t)‖ ^ 2) ∧
      Tendsto (fun s : ℝ => (∫ t in (0:ℝ)..1, ⟪ζ (s, t), fderiv ℝ ζ (s, t) (1, 0)⟫) /
        (∫ t in (0:ℝ)..1, ‖ζ (s, t)‖ ^ 2)) atTop (𝓝 μ) ∧
      Tendsto (fun s : ℝ => ∫ x in s..s + 1,
        ((∫ t in (0:ℝ)..1, ‖fderiv ℝ ζ (x, t) (1, 0)‖ ^ 2) / (∫ t in (0:ℝ)..1, ‖ζ (x, t)‖ ^ 2) -
          ((∫ t in (0:ℝ)..1, ⟪ζ (x, t), fderiv ℝ ζ (x, t) (1, 0)⟫) /
            (∫ t in (0:ℝ)..1, ‖ζ (x, t)‖ ^ 2)) ^ 2)) atTop (𝓝 0) := by
  sorry

end FiniteEnergyPlane
