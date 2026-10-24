-- Prove2me | Theorems.Thm_FiniteEnergyPlane_halfCyl_rescaled_exp_conv
-- name    : FiniteEnergyPlane.halfCyl_rescaled_exp_conv
-- status  : Proved
-- author  : @fizzyinc3
-- created : 2026-10-23T15:35:42.992577+00:00
-- url     : https://prove2.me/theorems/c56a49e0-416b-427d-ad04-ad76577515ea
-- title:
--   Rescaled linear Cauchy–Riemann solutions converge exponentially to an eigenfunction
-- statement:
--   Let $S:\mathbb{R}^2\to\mathbb{R}^{2n\times 2n}$ be $C^\infty$ and $1$-periodic in $t$, and let $S_\infty$ be a smooth $1$-periodic loop of symmetric matrices such that $S(s,t)\to S_\infty(t)$ exponentially fast in $C^\infty$ with rate $d>0$. Let $\zeta$ be a smooth, $t$-periodic solution of $\partial_s\zeta + J_0\partial_t\zeta + S\zeta = 0$ on $(0,\infty)\times\mathbb{R}$ that is not identically zero and satisfies $|\zeta(s,t)|\le C e^{\delta_0 s}$.
--
--   Then there are an eigenvalue $\mu\le\delta_0$ of the asymptotic operator $A_\infty=-J_0\partial_t-S_\infty$ and an eigenfunction $e$ ($A_\infty e=\mu e$, $e\not\equiv0$, smooth and $1$-periodic) such that the rescaled solution $\chi(s,t)=e^{-\mu s}\zeta(s,t)$ satisfies, for some $s_0>0$, $M$, $b>0$, $K$ and all $s\ge s_0$, $t\in\mathbb{R}$:
--   $$|\chi(s,t)-e(t)|\le Ke^{-bs},\qquad |\chi(s,t)|\le M,\qquad |\partial_s\chi(s,t)|\le M,\qquad |\partial_t\chi(s,t)|\le M .$$
--   This is the $C^0$ part of the linear asymptotic formula (Wendl Thm. 4.8.2); the $C^\infty$ upgrade follows by elliptic regularity.
-- source:
--   Wendl, Lectures on Symplectic Field Theory (2026 notes), proof of Theorem 4.8.2 (linear asymptotic formula); U. Hryniewicz, J. Symplectic Geom. 12 (2014), proof of Theorem 2.11 (the step showing that $e^{-\mu s}\zeta$ converges in $C^0$ at an exponential rate to an eigenfunction, with $C^1$ bounds)

import Mathlib
import Definitions.Def_FiniteEnergyPlane_Asymptotics

namespace FiniteEnergyPlane

open scoped ContDiff

/-- Stage of Wendl, Prop. 4.8.2 / Hryniewicz, Thm. 2.11: under the hypotheses of
`halfCyl_asymptotic_formula`, there are an eigenvalue `μ ≤ δ₀` and an eigenfunction `e` of
`-J₀ ∂ₜ - S∞` such that the rescaled solution `χ(s, t) = e^{-μs} ζ(s, t)` converges to `e(t)`
exponentially fast in `C⁰`, and `χ`, `∂ₛχ`, `∂ₜχ` are uniformly bounded for large `s`. -/
theorem halfCyl_rescaled_exp_conv {n : ℕ} (S : ℝ × ℝ → CauchyRiemannIndex.Mat n)
    (hS : ∀ i j, ContDiff ℝ ∞ (fun p : ℝ × ℝ => S p i j)) (hSper : ∀ s t : ℝ, S (s, t + 1) = S (s, t))
    (Sinf : ℝ → CauchyRiemannIndex.Mat n) (hSinf : CauchyRiemannIndex.IsSymLoop Sinf)
    (hSinf' : ∀ i j, ContDiff ℝ ∞ (fun t => Sinf t i j))
    (d : ℝ) (hd : 0 < d) (hSas : IsExpAsymptoticTo S Sinf d)
    (ζ : ℝ × ℝ → CauchyRiemannIndex.Vec n) (hζ : IsHalfCylSolution S ζ)
    (hne : ∃ p : ℝ × ℝ, 0 < p.1 ∧ ζ p ≠ 0)
    (C δ₀ : ℝ) (hgrowth : ∀ s > 0, ∀ t : ℝ, ‖ζ (s, t)‖ ≤ C * Real.exp (δ₀ * s)) :
    ∃ μ : ℝ, μ ≤ δ₀ ∧ ∃ e : ℝ → CauchyRiemannIndex.Vec n, IsLoopEigen Sinf μ e ∧
      ∃ s₀ > 0, ∃ M b K : ℝ, 0 < b ∧ ∀ s ≥ s₀, ∀ t : ℝ,
        ‖Real.exp (-(μ * s)) • ζ (s, t) - e t‖ ≤ K * Real.exp (-(b * s)) ∧
        ‖Real.exp (-(μ * s)) • ζ (s, t)‖ ≤ M ∧
        ‖fderiv ℝ (fun p : ℝ × ℝ => Real.exp (-(μ * p.1)) • ζ p) (s, t) (1, 0)‖ ≤ M ∧
        ‖fderiv ℝ (fun p : ℝ × ℝ => Real.exp (-(μ * p.1)) • ζ p) (s, t) (0, 1)‖ ≤ M := by sorry

end FiniteEnergyPlane
