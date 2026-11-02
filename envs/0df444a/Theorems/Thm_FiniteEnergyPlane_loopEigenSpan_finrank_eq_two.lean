-- Prove2me | Theorems.Thm_FiniteEnergyPlane_loopEigenSpan_finrank_eq_two
-- name    : FiniteEnergyPlane.loopEigenSpan_finrank_eq_two
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-11-01T15:37:11.718524+00:00
-- url     : https://prove2.me/theorems/7e1d7e00-f2f3-4804-9ec7-f250e5197034
-- title:
--   Each winding number belongs to a two-dimensional space of eigenfunctions
-- statement:
--   Let $S_\infty:\mathbb{R}\to\mathbb{R}^{2\times2}$ be a $C^\infty$ $1$-periodic loop of symmetric matrices and $A=-J_0\partial_t-S_\infty$ on $1$-periodic loops in $\mathbb{R}^2=\mathbb{C}$. For every $k\in\mathbb{Z}$, the eigenfunctions of $A$ whose eigenvalue has winding $k$ span a real vector space of dimension exactly $2$.
--
--   **Formalization Note** The span is `loopEigenSpan Sinf k`, a submodule of `ℝ → CauchyRiemannIndex.Vec 1`; the statement includes `FiniteDimensional`, so `Module.finrank` is the actual dimension.
-- source:
--   C. Wendl, Lectures on Symplectic Field Theory, lecture notes, Humboldt-Universität zu Berlin (2026 version); earlier version arXiv:1612.01009, Theorem 3.7.1 (4); H. Hofer, K. Wysocki, E. Zehnder, Properties of pseudoholomorphic curves in symplectisations II: Embedding controls and algebraic invariants, Geom. Funct. Anal. 5 (1995), 270–328, Section 3

import Definitions.Def_FiniteEnergyPlane_Winding

namespace FiniteEnergyPlane

open MeasureTheory Metric Filter Topology
open scoped ContDiff ENNReal Real

/-- Wendl, Theorem 3.7.1 (4): for every `k ∈ ℤ`, the eigenfunctions of `A = -J₀ ∂ₜ - S∞` with
winding number `k` span a real vector space of dimension exactly `2`. In particular every
winding number is attained, by one eigenvalue of multiplicity `2` or by two eigenvalues of
multiplicity `1`. -/
theorem loopEigenSpan_finrank_eq_two (Sinf : ℝ → CauchyRiemannIndex.Mat 1) (hSinf : CauchyRiemannIndex.IsSymLoop Sinf)
    (hSinf' : ∀ i j, ContDiff ℝ ∞ (fun t => Sinf t i j)) (k : ℤ) :
    FiniteDimensional ℝ (loopEigenSpan Sinf k) ∧ Module.finrank ℝ (loopEigenSpan Sinf k) = 2 := by
  sorry

end FiniteEnergyPlane
