-- Prove2me | Theorems.Thm_FiniteEnergyPlane_continuousAt_reeb
-- name    : FiniteEnergyPlane.continuousAt_reeb
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-11-25T13:07:50.166824+00:00
-- url     : https://prove2.me/theorems/8e84b4d0-9790-475b-be84-e3f4c123826c
-- title:
--   Continuity of the Reeb field
-- statement:
--   Let $S=H^{-1}(1)\subset\mathbb{R}^{2n+2}$ be a strictly star-shaped level. The Reeb field $R=X_H/\lambda_0(X_H)$, as a function on $\mathbb{R}^{2n+2}$, is continuous at every point of $S$.
--
--   Reusable for continuity arguments along Reeb trajectories.
-- source:
--   U. Hryniewicz, Fast finite-energy planes in symplectizations and applications, Trans. Amer. Math. Soc. 364 (2012), 1859-1931, arXiv:0812.4076, Section 7

import Definitions.Def_FiniteEnergyPlane_OpenBook

namespace FiniteEnergyPlane

open MeasureTheory Metric Filter Topology
open scoped ContDiff ENNReal Real

/-- The Reeb field formula is continuous at points of `S`. -/
theorem continuousAt_reeb {n : ℕ} (H : V n → ℝ) (hH : IsStrictlyStarShapedLevel H) (x : V n)
    (hx : x ∈ energySurface H) : ContinuousAt (reeb H) x := by
  sorry

end FiniteEnergyPlane
