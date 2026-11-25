-- Prove2me | Theorems.Thm_FiniteEnergyPlane_exists_isReebTrajectory
-- name    : FiniteEnergyPlane.exists_isReebTrajectory
-- status  : Open
-- author  : @Mazecto
-- created : 2026-11-25T10:09:07.224234+00:00
-- url     : https://prove2.me/theorems/e5f02405-fa41-4ef5-9951-4ed1f7db3d9a
-- title:
--   A complete Reeb trajectory through every point of a star-shaped level
-- statement:
--   Let $S=H^{-1}(1)\subset\mathbb{R}^{2n+2}$ be a strictly star-shaped level. For every $q\in S$ there is a Reeb trajectory $y:\mathbb{R}\to S$ with $y(0)=q$.
--
--   Reusable whenever a trajectory of the Reeb field with a prescribed initial point is needed.
--
--   **Formalization Note** A trajectory is `IsReebTrajectory H y`: $y(t)\in S$ and $y'(t)=R(y(t))$ for all $t\in\mathbb{R}$.
-- source:
--   U. Hryniewicz, Fast finite-energy planes in symplectizations and applications, Trans. Amer. Math. Soc. 364 (2012), 1859-1931, arXiv:0812.4076, Section 7

import Definitions.Def_FiniteEnergyPlane_OpenBook

namespace FiniteEnergyPlane

open MeasureTheory Metric Filter Topology
open scoped ContDiff ENNReal Real

/-- Through every point of a strictly star-shaped level `S = H⁻¹(1)` there is a Reeb trajectory
defined for all times. -/
theorem exists_isReebTrajectory {n : ℕ} (H : V n → ℝ) (hH : IsStrictlyStarShapedLevel H)
    (q : V n) (hq : q ∈ energySurface H) : ∃ y : ℝ → V n, IsReebTrajectory H y ∧ y 0 = q := by
  sorry

end FiniteEnergyPlane
