-- Prove2me | Theorems.Thm_FiniteEnergyPlane_halfCyl_asymptotic_formula
-- name    : FiniteEnergyPlane.halfCyl_asymptotic_formula
-- status  : Open
-- author  : @Mazecto
-- created : 2026-10-21T12:42:33.022193+00:00
-- url     : https://prove2.me/theorems/9d7619b0-d17e-42cb-ab93-0916eb2795f1
-- title:
--   Asymptotic formula for linear Cauchy–Riemann equations on a half-cylinder
-- statement:
--   Let $S:\mathbb{R}^2\to\mathbb{R}^{2n\times2n}$ be $C^\infty$ and $1$-periodic in $t$, $S_\infty$ a $C^\infty$ $1$-periodic loop of symmetric matrices, and $d>0$ with $S-S_\infty$ decaying like $e^{-ds}$ in $C^\infty$. Let $\zeta$ be a solution of $\partial_s\zeta+J_0\partial_t\zeta+S\zeta=0$ on the half-cylinder, not identically zero on $(0,\infty)\times\mathbb{R}$, with $\|\zeta(s,t)\|\le Ce^{\delta_0s}$ for $s>0$. Then there are an eigenvalue $\mu\le\delta_0$ of $-J_0\partial_t-S_\infty$ and an eigenfunction $e$ for $\mu$ such that $e^{-\mu s}\zeta(s,t)-e(t)\to0$ in $C^\infty$.
--
--   **Formalization Note** The eigenfunction is `IsLoopEigen Sinf μ e`; the convergence is `TendstoZeroCInfty` of `fun p => Real.exp (-(μ * p.1)) • ζ p - e p.2`.
-- source:
--   C. Wendl, Lectures on Symplectic Field Theory, lecture notes, Humboldt-Universität zu Berlin (2026 version); earlier version arXiv:1612.01009, Theorem 4.8.2, formula (4.26); R. Siefring, Relative asymptotic behavior of pseudoholomorphic half-cylinders, Comm. Pure Appl. Math. 61 (2008), arXiv:math/0702356, Appendix A

import Definitions.Def_FiniteEnergyPlane_Asymptotics

namespace FiniteEnergyPlane

open MeasureTheory Metric Filter Topology
open scoped ContDiff ENNReal Real

/-- Asymptotic formula for linear Cauchy–Riemann equations on a half-cylinder: if `S(s, t) - S∞(t)`
decays exponentially in `C^∞` and `ζ` is a solution of `∂ₛζ + J₀ ∂ₜζ + S ζ = 0`, not identically
zero, with `‖ζ(s, t)‖ ≤ C e^{δ₀ s}`, then there are an eigenvalue `μ ≤ δ₀` of `-J₀ ∂ₜ - S∞` and an
eigenfunction `e` with `e^{-μs} ζ(s, t) - e(t) → 0` in `C^∞`. -/
theorem halfCyl_asymptotic_formula {n : ℕ} (S : ℝ × ℝ → CauchyRiemannIndex.Mat n)
    (hS : ∀ i j, ContDiff ℝ ∞ (fun p : ℝ × ℝ => S p i j)) (hSper : ∀ s t : ℝ, S (s, t + 1) = S (s, t))
    (Sinf : ℝ → CauchyRiemannIndex.Mat n) (hSinf : CauchyRiemannIndex.IsSymLoop Sinf)
    (hSinf' : ∀ i j, ContDiff ℝ ∞ (fun t => Sinf t i j))
    (d : ℝ) (hd : 0 < d) (hSas : IsExpAsymptoticTo S Sinf d)
    (ζ : ℝ × ℝ → CauchyRiemannIndex.Vec n) (hζ : IsHalfCylSolution S ζ)
    (hne : ∃ p : ℝ × ℝ, 0 < p.1 ∧ ζ p ≠ 0)
    (C δ₀ : ℝ) (hgrowth : ∀ s > 0, ∀ t : ℝ, ‖ζ (s, t)‖ ≤ C * Real.exp (δ₀ * s)) :
    ∃ μ : ℝ, μ ≤ δ₀ ∧ ∃ e : ℝ → CauchyRiemannIndex.Vec n, IsLoopEigen Sinf μ e ∧
      TendstoZeroCInfty (fun p : ℝ × ℝ => Real.exp (-(μ * p.1)) • ζ p - e p.2) := by
  sorry

end FiniteEnergyPlane
