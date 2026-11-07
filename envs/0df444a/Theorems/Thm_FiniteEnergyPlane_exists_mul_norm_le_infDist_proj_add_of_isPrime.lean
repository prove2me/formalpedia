-- Prove2me | Theorems.Thm_FiniteEnergyPlane_exists_mul_norm_le_infDist_proj_add_of_isPrime
-- name    : FiniteEnergyPlane.exists_mul_norm_le_infDist_proj_add_of_isPrime
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-11-06T17:29:52.223032+00:00
-- url     : https://prove2.me/theorems/a823e827-f3e7-4353-9025-07276c8394e7
-- title:
--   Distance to a prime Reeb orbit in the tube around it is comparable to the normal coordinate
-- statement:
--   Let $P = (x, T)$ be a prime periodic Reeb orbit on a strictly star-shaped level $S$. There are $c, \rho > 0$ such that for every $\tau$ and every $h \in \xi_{x(\tau)}$ with $\|h\| \leq \rho$, the point $\mathrm{proj}(x(\tau) + h)$ has distance at least $c \|h\|$ from the image of $P$.
--
--   So in the tube coordinates $(\tau, h)$ around $P$, the normal coordinate is controlled by the distance to the orbit.
-- source:
--   U. Hryniewicz, Trans. AMS 364 (2012), § 6

import Definitions.Def_FiniteEnergyPlane_Winding

namespace FiniteEnergyPlane

open MeasureTheory Metric Filter Topology
open scoped ContDiff ENNReal Real

/-- Distance to a prime orbit in the tube around it. For a prime periodic Reeb orbit `P = (x, T)`
there are `c, ρ > 0` such that for every `τ` and every `h ∈ ξ_{x(τ)}` with `‖h‖ ≤ ρ`, the point
`proj (x(τ) + h)` has distance at least `c ‖h‖` from the image of `P`. -/
theorem exists_mul_norm_le_infDist_proj_add_of_isPrime {n : ℕ} (H : V n → ℝ)
    (hH : IsStrictlyStarShapedLevel H) (J : V n → V n →L[ℝ] V n)
    (hJ : IsCompatibleXiStructure H J) (P : ReebOrbit H) (hP : P.IsPrime) :
    ∃ c > 0, ∃ ρ > 0, ∀ (τ : ℝ) (h : V n), IsInXi H (P.x τ) h → ‖h‖ ≤ ρ →
      c * ‖h‖ ≤ infDist (proj H (P.x τ + h)) (Set.range P.x) := by
  sorry

end FiniteEnergyPlane
