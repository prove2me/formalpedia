-- Prove2me | Theorems.Thm_FiniteEnergyPlane_exists_eigenEq_solution
-- name    : FiniteEnergyPlane.exists_eigenEq_solution
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-11-01T21:47:09.865461+00:00
-- url     : https://prove2.me/theorems/5ae82701-f8f8-425b-b071-b9b92e6c17c8
-- title:
--   Solutions of the eigenvalue equation of the asymptotic operator on the line with prescribed initial value
-- statement:
--   Let $S:\mathbb{R}\to\mathbb{R}^{2n\times2n}$ be continuous, $J_0=\begin{pmatrix}0&-\mathrm{Id}\\\mathrm{Id}&0\end{pmatrix}$, $\mu\in\mathbb{R}$ and $v\in\mathbb{R}^{2n}$. Then there is a differentiable $x:\mathbb{R}\to\mathbb{R}^{2n}$ with $x(0)=v$ and
--   $$-J_0x'(t)-S(t)x(t)=\mu\,x(t)\qquad\text{for all }t\in\mathbb{R}.$$
--
--   Global solvability of the initial value problem for the eigenvalue equation of the operator $-J_0\partial_t-S$ on the whole line (no periodicity required); it provides the non-periodic solutions used to study the eigenvalues of the asymptotic operator.
--
--   **Formalization Note** $\mathbb{R}^{2n}$ is `CauchyRiemannIndex.Vec n` and matrices are `CauchyRiemannIndex.Mat n`; $J_0$ is `CauchyRiemannIndex.J₀ n` and matrices act through `Matrix.toEuclideanLin`; the derivative is `deriv x t` together with `Differentiable ℝ x`.
-- source:
--   C. Wendl, Lectures on Symplectic Field Theory (2026 notes), arXiv:1612.01009, Sections 3.4 and 3.7; standard linear ODE theory.

import Definitions.Def_FiniteEnergyPlane_Winding

namespace FiniteEnergyPlane

/-- For continuous `S : ℝ → ℝ^{2n×2n}`, `μ ∈ ℝ` and `v ∈ ℝ^{2n}`, the equation
`-J₀ x' - S x = μ x` has a differentiable solution `x : ℝ → ℝ^{2n}` on all of `ℝ` with
`x 0 = v`. -/
theorem exists_eigenEq_solution {n : ℕ} (S : ℝ → CauchyRiemannIndex.Mat n) (hS : Continuous S)
    (μ : ℝ) (v : CauchyRiemannIndex.Vec n) :
    ∃ x : ℝ → CauchyRiemannIndex.Vec n, x 0 = v ∧ Differentiable ℝ x ∧
      ∀ t, -(Matrix.toEuclideanLin (CauchyRiemannIndex.J₀ n) (deriv x t)) -
        Matrix.toEuclideanLin (S t) (x t) = μ • x t := by
  sorry

end FiniteEnergyPlane
