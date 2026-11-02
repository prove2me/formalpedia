-- Prove2me | Theorems.Thm_FiniteEnergyPlane_mul_im_conj_pos_of_eigenEq
-- name    : FiniteEnergyPlane.mul_im_conj_pos_of_eigenEq
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-11-01T21:52:34.135726+00:00
-- url     : https://prove2.me/theorems/8eb3af31-b9c8-4c1d-993e-6240c8c72773
-- title:
--   Comparison of solutions of the eigenvalue equation of the asymptotic operator for two parameters
-- statement:
--   Let $S:\mathbb{R}\to\mathbb{R}^{2\times2}$ take symmetric values, $J_0=\begin{pmatrix}0&-1\\1&0\end{pmatrix}$, and $\mu\neq\nu$. Let $e,f,x:\mathbb{R}\to\mathbb{R}^2=\mathbb{C}$ be differentiable (not necessarily periodic) with
--   $$-J_0e'-Se=\mu e,\qquad -J_0f'-Sf=\nu f,\qquad -J_0x'-Sx=\nu x,$$
--   $x(0)=e(0)$, and $f(t)$ not a real multiple of $e(t)$ for every $t\in[0,1]$, i.e. $\operatorname{Im}\big(\overline{f(t)}\,e(t)\big)\neq0$. Then
--   $$(\nu-\mu)\,\operatorname{Im}\big(\overline{e(1)}\,x(1)\big)>0.$$
--
--   A comparison statement for the eigenvalue equation of the asymptotic operator $-J_0\partial_t-S$: it fixes on which side of $e(1)$ the solution with parameter $\nu$ and initial value $e(0)$ ends up at time $1$, in terms of the sign of $\nu-\mu$.
--
--   **Formalization Note** Solutions are maps `ℝ → CauchyRiemannIndex.Vec 1` with `Differentiable ℝ` and the equation stated with `deriv` and `Matrix.toEuclideanLin`; symmetry is `∀ t, (S t).IsSymm`; $\mathbb{R}^2\to\mathbb{C}$ is `vecToC` (`FiniteEnergyPlane_Winding`).
-- source:
--   C. Wendl, Lectures on Symplectic Field Theory (2026 notes), arXiv:1612.01009, Section 3.7, proof of Theorem 3.7.1; H. Hofer, K. Wysocki, E. Zehnder, GAFA 5 (1995), Section 3.

import Definitions.Def_FiniteEnergyPlane_Winding

namespace FiniteEnergyPlane

/-- Let `S : ℝ → ℝ^{2×2}` take symmetric values and `μ ≠ ν`. Let `e` solve
`-J₀ e' - S e = μ e`, and let `f`, `x` solve `-J₀ y' - S y = ν y` on `ℝ` (differentiable,
not necessarily periodic), with `x 0 = e 0` and `f t` never a real multiple of `e t` for
`t ∈ [0, 1]`. Read in `ℂ`, `(ν - μ) Im(conj e(1) · x(1)) > 0`. -/
theorem mul_im_conj_pos_of_eigenEq (S : ℝ → CauchyRiemannIndex.Mat 1)
    (hS : ∀ t, (S t).IsSymm) {μ ν : ℝ} (hμν : μ ≠ ν) {e f x : ℝ → CauchyRiemannIndex.Vec 1}
    (he : Differentiable ℝ e)
    (hee : ∀ t, -(Matrix.toEuclideanLin (CauchyRiemannIndex.J₀ 1) (deriv e t)) -
      Matrix.toEuclideanLin (S t) (e t) = μ • e t)
    (hf : Differentiable ℝ f)
    (hfe : ∀ t, -(Matrix.toEuclideanLin (CauchyRiemannIndex.J₀ 1) (deriv f t)) -
      Matrix.toEuclideanLin (S t) (f t) = ν • f t)
    (hx : Differentiable ℝ x)
    (hxe : ∀ t, -(Matrix.toEuclideanLin (CauchyRiemannIndex.J₀ 1) (deriv x t)) -
      Matrix.toEuclideanLin (S t) (x t) = ν • x t)
    (hx0 : x 0 = e 0)
    (hfe0 : ∀ t ∈ Set.Icc (0 : ℝ) 1, (starRingEnd ℂ (vecToC (f t)) * vecToC (e t)).im ≠ 0) :
    0 < (ν - μ) * (starRingEnd ℂ (vecToC (e 1)) * vecToC (x 1)).im := by
  sorry

end FiniteEnergyPlane
