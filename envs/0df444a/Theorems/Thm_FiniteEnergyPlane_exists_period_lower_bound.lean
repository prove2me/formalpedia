-- Prove2me | Theorems.Thm_FiniteEnergyPlane_exists_period_lower_bound
-- name    : FiniteEnergyPlane.exists_period_lower_bound
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-10-20T23:23:26.480132+00:00
-- url     : https://prove2.me/theorems/50cb7545-a94b-4a0d-b1a2-0ec96f64a835
-- title:
--   Periods of Reeb orbits on a star-shaped level are bounded away from zero
-- statement:
--   Let $S=H^{-1}(1)\subset\mathbb{R}^{2n+2}$ be a strictly star-shaped level. There is $T_0>0$ such that $T\ge T_0$ for every periodic Reeb orbit $(x,T)$ on $S$.
--
--   **Formalization Note** Periods are not required to be minimal (`ReebOrbit` allows multiple covers), which does not affect the statement.
-- source:
--   Standard fact for a compact contact-type hypersurface; stated in U. Hryniewicz, Systems of global surfaces of section for dynamically convex Reeb flows on the 3-sphere, J. Symplectic Geom. 12 (2014), arXiv:1105.2077, p. 26

import Definitions.Def_FiniteEnergyPlane_Setting

namespace FiniteEnergyPlane

open MeasureTheory Metric Filter Topology
open scoped ContDiff ENNReal Real

/-- Periods of Reeb orbits on a strictly star-shaped level are bounded away from `0`: there is
`T₀ > 0` with `T₀ ≤ T` for every periodic Reeb orbit `(x, T)` on `S`. -/
theorem exists_period_lower_bound {n : ℕ} (H : V n → ℝ) (hH : IsStrictlyStarShapedLevel H) :
    ∃ T₀ : ℝ, 0 < T₀ ∧ ∀ P : ReebOrbit H, T₀ ≤ P.T := by
  sorry

end FiniteEnergyPlane
