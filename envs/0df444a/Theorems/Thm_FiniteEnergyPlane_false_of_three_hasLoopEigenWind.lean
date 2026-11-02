-- Prove2me | Theorems.Thm_FiniteEnergyPlane_false_of_three_hasLoopEigenWind
-- name    : FiniteEnergyPlane.false_of_three_hasLoopEigenWind
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-11-01T21:24:20.389036+00:00
-- url     : https://prove2.me/theorems/60d67343-8504-4f1a-8646-a4bfcd881e88
-- title:
--   No winding number is shared by three distinct eigenvalues of the asymptotic operator
-- statement:
--   Let $S_\infty:\mathbb{R}\to\mathbb{R}^{2\times2}$ be a $C^\infty$ $1$-periodic loop of symmetric matrices and $A=-J_0\partial_t-S_\infty$ on $1$-periodic loops in $\mathbb{R}^2$. Let $k\in\mathbb{Z}$. There are no three eigenvalues $\mu_1<\mu_2<\mu_3$ of $A$ such that, for each $j$, every eigenfunction of $\mu_j$ has winding number $k$.
--
--   The finiteness half of the statement that each winding number belongs to a two-dimensional space of eigenfunctions (Wendl, Theorem 3.7.1 (4)): at most two eigenvalues have a given winding number.
--
--   **Formalization Note** "$\mu$ is an eigenvalue all of whose eigenfunctions have winding $k$" is `HasLoopEigenWind Sinf μ k` (`FiniteEnergyPlane_Winding`; eigenfunctions are `IsLoopEigen`, `FiniteEnergyPlane_Asymptotics`); the conclusion is `False` under the three hypotheses.
-- source:
--   C. Wendl, Lectures on Symplectic Field Theory (2026 notes), arXiv:1612.01009, Section 3.7, Theorem 3.7.1 (4); H. Hofer, K. Wysocki, E. Zehnder, GAFA 5 (1995), Section 3.

import Definitions.Def_FiniteEnergyPlane_Winding

namespace FiniteEnergyPlane

open scoped ContDiff

/-- No winding number `k` is shared by three distinct eigenvalues `μ₁ < μ₂ < μ₃` of
`A = -J₀ ∂ₜ - S∞`. -/
theorem false_of_three_hasLoopEigenWind (Sinf : ℝ → CauchyRiemannIndex.Mat 1)
    (hSinf : CauchyRiemannIndex.IsSymLoop Sinf)
    (hSinf' : ∀ i j, ContDiff ℝ ∞ (fun t => Sinf t i j)) {μ₁ μ₂ μ₃ : ℝ} {k : ℤ}
    (h₁₂ : μ₁ < μ₂) (h₂₃ : μ₂ < μ₃) (h₁ : HasLoopEigenWind Sinf μ₁ k)
    (h₂ : HasLoopEigenWind Sinf μ₂ k) (h₃ : HasLoopEigenWind Sinf μ₃ k) : False := by
  sorry

end FiniteEnergyPlane
