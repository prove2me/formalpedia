-- Prove2me | Theorems.Thm_FiniteEnergyPlane_exists_isLoopEigen_hasLoopEigenWind_linearIndependent
-- name    : FiniteEnergyPlane.exists_isLoopEigen_hasLoopEigenWind_linearIndependent
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-11-01T21:24:21.864479+00:00
-- url     : https://prove2.me/theorems/770c4cc9-9a99-40ea-93fc-ff0d30cd24f2
-- title:
--   Every winding number is carried by eigenfunctions with linearly independent initial values
-- statement:
--   Let $S_\infty:\mathbb{R}\to\mathbb{R}^{2\times2}$ be a $C^\infty$ $1$-periodic loop of symmetric matrices and $A=-J_0\partial_t-S_\infty$ on $1$-periodic loops in $\mathbb{R}^2$. For every $k\in\mathbb{Z}$ there are eigenvalues $\mu_1,\mu_2$ of $A$ (possibly equal), each of whose eigenfunctions all have winding number $k$, and eigenfunctions $e_1,e_2$ with eigenvalues $\mu_1,\mu_2$ such that $e_1(0),e_2(0)$ are linearly independent in $\mathbb{R}^2$.
--
--   The existence half of the statement that each winding number belongs to a two-dimensional space of eigenfunctions (Wendl, Theorem 3.7.1 (4)). In particular every integer is the winding number of some eigenvalue.
--
--   **Formalization Note** Eigenfunctions are `IsLoopEigen Sinf μ e` (`FiniteEnergyPlane_Asymptotics`: smooth, $1$-periodic, not identically zero, $-J_0e'-S_\infty e=\mu e$); "all eigenfunctions of $\mu$ have winding $k$" is `HasLoopEigenWind Sinf μ k` (`FiniteEnergyPlane_Winding`); independence is `LinearIndependent ℝ ![e₁ 0, e₂ 0]`.
-- source:
--   C. Wendl, Lectures on Symplectic Field Theory (2026 notes), arXiv:1612.01009, Section 3.7, Theorem 3.7.1 (4); H. Hofer, K. Wysocki, E. Zehnder, GAFA 5 (1995), Section 3.

import Definitions.Def_FiniteEnergyPlane_Winding

namespace FiniteEnergyPlane

open scoped ContDiff

/-- For every `k ∈ ℤ` there are eigenfunctions `e₁, e₂` of `A = -J₀ ∂ₜ - S∞`, with (possibly
equal) eigenvalues `μ₁, μ₂` both of winding number `k`, whose initial values `e₁ 0, e₂ 0` are
linearly independent in `ℝ²`. -/
theorem exists_isLoopEigen_hasLoopEigenWind_linearIndependent
    (Sinf : ℝ → CauchyRiemannIndex.Mat 1) (hSinf : CauchyRiemannIndex.IsSymLoop Sinf)
    (hSinf' : ∀ i j, ContDiff ℝ ∞ (fun t => Sinf t i j)) (k : ℤ) :
    ∃ μ₁ μ₂ : ℝ, ∃ e₁ e₂ : ℝ → CauchyRiemannIndex.Vec 1,
      IsLoopEigen Sinf μ₁ e₁ ∧ IsLoopEigen Sinf μ₂ e₂ ∧ HasLoopEigenWind Sinf μ₁ k ∧
        HasLoopEigenWind Sinf μ₂ k ∧ LinearIndependent ℝ ![e₁ 0, e₂ 0] := by
  sorry

end FiniteEnergyPlane
