-- Prove2me | Theorems.Thm_FiniteEnergyPlane_loopEigen_apply_ne_smul_of_hasLoopEigenWind
-- name    : FiniteEnergyPlane.loopEigen_apply_ne_smul_of_hasLoopEigenWind
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-11-01T21:23:36.590288+00:00
-- url     : https://prove2.me/theorems/0f9d72c0-18f0-40f0-b5cf-a5e922c54ad0
-- title:
--   Eigenfunctions of distinct eigenvalues with the same winding number are never parallel
-- statement:
--   Let $S_\infty:\mathbb{R}\to\mathbb{R}^{2\times2}$ be a $C^\infty$ $1$-periodic loop of symmetric matrices and $A=-J_0\partial_t-S_\infty$ on $1$-periodic loops in $\mathbb{R}^2$. Let $\mu_1\ne\mu_2$ be eigenvalues of $A$ such that every eigenfunction of $\mu_1$ and every eigenfunction of $\mu_2$ has the same winding number $k\in\mathbb{Z}$. If $e_1,e_2$ are eigenfunctions with eigenvalues $\mu_1,\mu_2$, then for every $t\in\mathbb{R}$ and every $c\in\mathbb{R}$,
--   $$e_2(t)\ne c\,e_1(t).$$
--
--   The values of such eigenfunctions are linearly independent in $\mathbb{R}^2$ at every time. This controls how eigenfunctions of one winding number can combine.
--
--   **Formalization Note** Eigenfunctions are `IsLoopEigen Sinf μ e` (`FiniteEnergyPlane_Asymptotics`); the winding hypothesis on $\mu_j$ is `HasLoopEigenWind Sinf μⱼ k` (`FiniteEnergyPlane_Winding`: $\mu_j$ has an eigenfunction and all its eigenfunctions have winding $k$ as loops in $\mathbb{C}$ via `vecToC`); `IsSymLoop Sinf` and smoothness of the entries are hypotheses.
-- source:
--   C. Wendl, Lectures on Symplectic Field Theory (2026 notes), arXiv:1612.01009, Section 3.7, Theorem 3.7.1; H. Hofer, K. Wysocki, E. Zehnder, GAFA 5 (1995), Section 3.

import Definitions.Def_FiniteEnergyPlane_Winding

namespace FiniteEnergyPlane

open scoped ContDiff

/-- Eigenfunctions of `A = -J₀ ∂ₜ - S∞` for two distinct eigenvalues with the same winding
number are pointwise linearly independent: their values are never parallel. -/
theorem loopEigen_apply_ne_smul_of_hasLoopEigenWind (Sinf : ℝ → CauchyRiemannIndex.Mat 1)
    (hSinf : CauchyRiemannIndex.IsSymLoop Sinf)
    (hSinf' : ∀ i j, ContDiff ℝ ∞ (fun t => Sinf t i j)) {μ₁ μ₂ : ℝ} {k : ℤ} (hμ : μ₁ ≠ μ₂)
    (h₁ : HasLoopEigenWind Sinf μ₁ k) (h₂ : HasLoopEigenWind Sinf μ₂ k)
    {e₁ e₂ : ℝ → CauchyRiemannIndex.Vec 1} (he₁ : IsLoopEigen Sinf μ₁ e₁)
    (he₂ : IsLoopEigen Sinf μ₂ e₂) (t c : ℝ) : e₂ t ≠ c • e₁ t := by
  sorry

end FiniteEnergyPlane
