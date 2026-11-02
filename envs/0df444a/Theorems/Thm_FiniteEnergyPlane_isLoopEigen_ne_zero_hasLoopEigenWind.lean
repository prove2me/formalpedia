-- Prove2me | Theorems.Thm_FiniteEnergyPlane_isLoopEigen_ne_zero_hasLoopEigenWind
-- name    : FiniteEnergyPlane.isLoopEigen_ne_zero_hasLoopEigenWind
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-11-01T15:36:35.513848+00:00
-- url     : https://prove2.me/theorems/5f2b8aab-a05f-4bea-9db0-cd1fa8a23467
-- title:
--   Eigenfunctions of asymptotic operators on $\mathbb{R}^2$ have no zeros and a common winding
-- statement:
--   Let $S_\infty:\mathbb{R}\to\mathbb{R}^{2\times2}$ be a $C^\infty$ $1$-periodic loop of symmetric matrices and $A=-J_0\partial_t-S_\infty$ on $1$-periodic loops in $\mathbb{R}^2=\mathbb{C}$. Every eigenfunction $e$ of $A$ vanishes nowhere, and all eigenfunctions of the same eigenvalue $\mu$ have the same winding number.
--
--   **Formalization Note** Eigenfunctions are `IsLoopEigen Sinf μ e` of `FiniteEnergyPlane_Asymptotics` with `n = 1`; the common winding is `HasLoopEigenWind Sinf μ k` for some `k`.
-- source:
--   C. Wendl, Lectures on Symplectic Field Theory, lecture notes, Humboldt-Universität zu Berlin (2026 version); earlier version arXiv:1612.01009, Theorem 3.7.1 (1), (2); H. Hofer, K. Wysocki, E. Zehnder, Properties of pseudoholomorphic curves in symplectisations II: Embedding controls and algebraic invariants, Geom. Funct. Anal. 5 (1995), 270–328, Section 3

import Definitions.Def_FiniteEnergyPlane_Winding

namespace FiniteEnergyPlane

open MeasureTheory Metric Filter Topology
open scoped ContDiff ENNReal Real

/-- Wendl, Theorem 3.7.1 (1)–(2), after Hofer–Wysocki–Zehnder: for a smooth loop `S∞` of symmetric
`2 × 2` matrices, every eigenfunction of `A = -J₀ ∂ₜ - S∞` vanishes nowhere, and all eigenfunctions
of one eigenvalue have the same winding number. -/
theorem isLoopEigen_ne_zero_hasLoopEigenWind (Sinf : ℝ → CauchyRiemannIndex.Mat 1) (hSinf : CauchyRiemannIndex.IsSymLoop Sinf)
    (hSinf' : ∀ i j, ContDiff ℝ ∞ (fun t => Sinf t i j)) (μ : ℝ)
    (e : ℝ → CauchyRiemannIndex.Vec 1) (he : IsLoopEigen Sinf μ e) :
    (∀ t : ℝ, e t ≠ 0) ∧ ∃ k : ℤ, HasLoopEigenWind Sinf μ k := by
  sorry

end FiniteEnergyPlane
