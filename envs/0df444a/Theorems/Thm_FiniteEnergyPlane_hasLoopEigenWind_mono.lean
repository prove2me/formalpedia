-- Prove2me | Theorems.Thm_FiniteEnergyPlane_hasLoopEigenWind_mono
-- name    : FiniteEnergyPlane.hasLoopEigenWind_mono
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-11-01T15:36:52.928926+00:00
-- url     : https://prove2.me/theorems/6de5535d-4ed1-4f7f-9a76-a1ed8e81b6bf
-- title:
--   The winding of eigenfunctions is monotone in the eigenvalue
-- statement:
--   Let $S_\infty:\mathbb{R}\to\mathbb{R}^{2\times2}$ be a $C^\infty$ $1$-periodic loop of symmetric matrices and $A=-J_0\partial_t-S_\infty$ on $1$-periodic loops in $\mathbb{R}^2=\mathbb{C}$. If $\mu_1<\mu_2$ are eigenvalues of $A$ with windings $k_1$ and $k_2$, then $k_1\le k_2$.
-- source:
--   C. Wendl, Lectures on Symplectic Field Theory, lecture notes, Humboldt-Universität zu Berlin (2026 version); earlier version arXiv:1612.01009, Theorem 3.7.1 (3); H. Hofer, K. Wysocki, E. Zehnder, Properties of pseudoholomorphic curves in symplectisations II: Embedding controls and algebraic invariants, Geom. Funct. Anal. 5 (1995), 270–328, Section 3

import Definitions.Def_FiniteEnergyPlane_Winding

namespace FiniteEnergyPlane

open MeasureTheory Metric Filter Topology
open scoped ContDiff ENNReal Real

/-- Wendl, Theorem 3.7.1 (3): the winding number of the eigenfunctions of `A = -J₀ ∂ₜ - S∞` is a
nondecreasing function of the eigenvalue. -/
theorem hasLoopEigenWind_mono (Sinf : ℝ → CauchyRiemannIndex.Mat 1) (hSinf : CauchyRiemannIndex.IsSymLoop Sinf)
    (hSinf' : ∀ i j, ContDiff ℝ ∞ (fun t => Sinf t i j)) {μ₁ μ₂ : ℝ} {k₁ k₂ : ℤ}
    (h₁ : HasLoopEigenWind Sinf μ₁ k₁) (h₂ : HasLoopEigenWind Sinf μ₂ k₂) (hμ : μ₁ < μ₂) :
    k₁ ≤ k₂ := by
  sorry

end FiniteEnergyPlane
