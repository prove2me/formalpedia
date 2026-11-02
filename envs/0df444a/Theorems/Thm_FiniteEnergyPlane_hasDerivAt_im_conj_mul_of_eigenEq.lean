-- Prove2me | Theorems.Thm_FiniteEnergyPlane_hasDerivAt_im_conj_mul_of_eigenEq
-- name    : FiniteEnergyPlane.hasDerivAt_im_conj_mul_of_eigenEq
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-11-01T21:42:21.047697+00:00
-- url     : https://prove2.me/theorems/97db8d46-5026-4565-aa3e-abce78e6f058
-- title:
--   Derivative of the cross term of two solutions of the eigenvalue equation on the line
-- statement:
--   Let $S:\mathbb{R}\to\mathbb{R}^{2\times2}$ take symmetric values, let $J_0=\begin{pmatrix}0&-1\\1&0\end{pmatrix}$, and let $\mu_1,\mu_2\in\mathbb{R}$. Let $x,y:\mathbb{R}\to\mathbb{R}^2=\mathbb{C}$ be differentiable maps (not necessarily periodic) with $-J_0x'-Sx=\mu_1x$ and $-J_0y'-Sy=\mu_2y$ on $\mathbb{R}$. Then for every $t$,
--   $$\frac{d}{dt}\operatorname{Im}\big(\overline{x(t)}\,y(t)\big)=(\mu_2-\mu_1)\operatorname{Re}\big(\overline{x(t)}\,y(t)\big).$$
--   In particular, for $\mu_1=\mu_2$ the quantity $\operatorname{Im}(\overline{x}\,y)$ is constant.
--
--   A differential identity for pairs of solutions of the eigenvalue equation of the asymptotic operator $-J_0\partial_t-S$ on the whole line, extending the corresponding identity for periodic eigenfunctions to arbitrary solutions.
--
--   **Formalization Note** $x$, $y$ are `ℝ → CauchyRiemannIndex.Vec 1` with `Differentiable ℝ` and the equation stated with `deriv` and `Matrix.toEuclideanLin`; symmetry is `∀ t, (S t).IsSymm` (no continuity or periodicity assumed); $\mathbb{R}^2\to\mathbb{C}$ is `vecToC` (`FiniteEnergyPlane_Winding`), and the conclusion is a `HasDerivAt` statement at every `t`.
-- source:
--   C. Wendl, Lectures on Symplectic Field Theory (2026 notes), arXiv:1612.01009, Section 3.7, proof of Theorem 3.7.1; H. Hofer, K. Wysocki, E. Zehnder, GAFA 5 (1995), Section 3.

import Definitions.Def_FiniteEnergyPlane_Winding

namespace FiniteEnergyPlane

/-- Let `S : ℝ → ℝ^{2×2}` take symmetric values and let `x, y : ℝ → ℝ²` be differentiable
solutions on `ℝ` (not necessarily periodic) of `-J₀ x' - S x = μ₁ x` and `-J₀ y' - S y = μ₂ y`.
Read as maps into `ℂ`, the imaginary part of `conj x · y` has derivative
`(μ₂ - μ₁) Re(conj x · y)`. -/
theorem hasDerivAt_im_conj_mul_of_eigenEq (S : ℝ → CauchyRiemannIndex.Mat 1)
    (hS : ∀ t, (S t).IsSymm) {μ₁ μ₂ : ℝ} {x y : ℝ → CauchyRiemannIndex.Vec 1}
    (hx : Differentiable ℝ x)
    (hxe : ∀ t, -(Matrix.toEuclideanLin (CauchyRiemannIndex.J₀ 1) (deriv x t)) -
      Matrix.toEuclideanLin (S t) (x t) = μ₁ • x t)
    (hy : Differentiable ℝ y)
    (hye : ∀ t, -(Matrix.toEuclideanLin (CauchyRiemannIndex.J₀ 1) (deriv y t)) -
      Matrix.toEuclideanLin (S t) (y t) = μ₂ • y t) (t : ℝ) :
    HasDerivAt (fun s => (starRingEnd ℂ (vecToC (x s)) * vecToC (y s)).im)
      ((μ₂ - μ₁) * (starRingEnd ℂ (vecToC (x t)) * vecToC (y t)).re) t := by
  sorry

end FiniteEnergyPlane
