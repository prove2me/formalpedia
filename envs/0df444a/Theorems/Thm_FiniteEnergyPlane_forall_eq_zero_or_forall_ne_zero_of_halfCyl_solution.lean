-- Prove2me | Theorems.Thm_FiniteEnergyPlane_forall_eq_zero_or_forall_ne_zero_of_halfCyl_solution
-- name    : FiniteEnergyPlane.forall_eq_zero_or_forall_ne_zero_of_halfCyl_solution
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-11-06T13:29:25.73306+00:00
-- url     : https://prove2.me/theorems/8a3578c8-1ff1-436c-aa2f-9786fecc2b1b
-- title:
--   A Cauchy-Riemann solution on the plane with small asymptotic winding vanishes identically or nowhere
-- statement:
--   Let $\zeta : \mathbb{C} \to \mathbb{C}$ be smooth, and suppose that near every point $|\partial_s \zeta + i\, \partial_t \zeta| \le M |\zeta|$ for some constant $M$ (depending on the point).
--
--   Suppose that at $\infty$ the map $\zeta$ is described in the cylindrical coordinates $z = e^{2\pi(s + it)}$ (`cylInf`) by a solution $w$ of $\partial_s w + J_0 \partial_t w + S w = 0$ on $s > 0$, $1$-periodic in $t$, where $S(s,t) - S_\infty(t)$ decays exponentially in $C^\infty$ to a smooth symmetric loop $S_\infty$, and $\|w(s,t)\| \le C e^{\delta s}$. Suppose finally that every eigenvalue $\mu \le \delta$ of $-J_0 \partial_t - S_\infty$ has winding number at most $0$.
--
--   Then $\zeta$ is identically zero, or $\zeta$ has no zeros.
--
--   **Role.** Solutions of linear Cauchy–Riemann type on the plane, with a prescribed growth bound at the end, either vanish identically or vanish nowhere. It applies, for example, to kernel elements of linearized operators along finite-energy planes.
--
--   **Formalization Note.** The identification of $\mathbb{R}^2$ with $\mathbb{C}$ is `vecToC`, and "every eigenvalue $\mu \le \delta$ has winding number at most $0$" is `HasLoopEigenWind Sinf μ k → k ≤ 0`. The bound `M` is local, so no uniform control on all of $\mathbb{C}$ is required. The operator $J_0$ is constant here.
-- source:
--   H. Hofer, K. Wysocki, E. Zehnder, Properties of pseudoholomorphic curves in symplectizations III: Fredholm theory (1999), Theorem 2.11; U. Hryniewicz, Fast finite-energy planes in symplectizations and applications, Trans. AMS 364 (2012), arXiv:0812.4076, Section 6

import Definitions.Def_FiniteEnergyPlane_Winding

namespace FiniteEnergyPlane

open Metric
open scoped ContDiff

/-- Let `ζ : ℂ → ℂ` be smooth with `|∂ₛζ + i ∂ₜζ| ≤ M |ζ|` locally. Suppose that at `∞`, in the
cylindrical coordinates `cylInf`, it is a solution `w` of `∂ₛw + J₀ ∂ₜw + S w = 0` on `s > 0`, where
`S(s, t) - S∞(t)` decays exponentially in `C^∞` to a symmetric loop `S∞`, with `‖w(s, t)‖ ≤ C e^{δs}`,
and that every eigenvalue `μ ≤ δ` of `-J₀ ∂ₜ - S∞` has winding number at most `0`. Then `ζ` is
identically zero or has no zeros. -/
theorem forall_eq_zero_or_forall_ne_zero_of_halfCyl_solution (ζ : ℂ → ℂ) (hζ : ContDiff ℝ ∞ ζ)
    (hM : ∀ z₀ : ℂ, ∃ ρ > (0 : ℝ), ∃ M : ℝ, ∀ z ∈ ball z₀ ρ,
      ‖fderiv ℝ ζ z 1 + Complex.I * fderiv ℝ ζ z Complex.I‖ ≤ M * ‖ζ z‖)
    (S : ℝ × ℝ → CauchyRiemannIndex.Mat 1)
    (hS : ∀ i j, ContDiff ℝ ∞ (fun p : ℝ × ℝ => S p i j)) (hSper : ∀ s t : ℝ, S (s, t + 1) = S (s, t))
    (Sinf : ℝ → CauchyRiemannIndex.Mat 1) (hSinf : CauchyRiemannIndex.IsSymLoop Sinf)
    (hSinf' : ∀ i j, ContDiff ℝ ∞ (fun t => Sinf t i j))
    (d : ℝ) (hd : 0 < d) (hSas : IsExpAsymptoticTo S Sinf d)
    (w : ℝ × ℝ → CauchyRiemannIndex.Vec 1) (hw : IsHalfCylSolution S w)
    (hwz : ∀ s > 0, ∀ t : ℝ, vecToC (w (s, t)) = ζ (cylInf s t))
    (C δ : ℝ) (hgrowth : ∀ s > 0, ∀ t : ℝ, ‖w (s, t)‖ ≤ C * Real.exp (δ * s))
    (hwind : ∀ μ ≤ δ, ∀ k : ℤ, HasLoopEigenWind Sinf μ k → k ≤ 0) :
    (∀ z, ζ z = 0) ∨ ∀ z, ζ z ≠ 0 := by
  sorry

end FiniteEnergyPlane
