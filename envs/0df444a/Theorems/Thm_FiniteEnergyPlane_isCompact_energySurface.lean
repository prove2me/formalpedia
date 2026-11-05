-- Prove2me | Theorems.Thm_FiniteEnergyPlane_isCompact_energySurface
-- name    : FiniteEnergyPlane.isCompact_energySurface
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-11-04T16:08:28.373164+00:00
-- url     : https://prove2.me/theorems/27c9097c-d3b1-4e1e-a49d-422de46aa15d
-- title:
--   A strictly star-shaped level is compact
-- statement:
--   Let $S=H^{-1}(1)\subset\mathbb{R}^{2n+2}$ be a strictly star-shaped level. Then $S$ is compact.
-- source:
--   U. Hryniewicz, Fast finite-energy planes in symplectizations and applications, Trans. Amer. Math. Soc. 364 (2012), 1859-1931, § 4.4

import Definitions.Def_FiniteEnergyPlane_Setting

namespace FiniteEnergyPlane

open MeasureTheory Metric Filter Topology
open scoped ContDiff ENNReal Real

/-- A strictly star-shaped level `S = H⁻¹(1)` is compact. -/
theorem isCompact_energySurface {n : ℕ} (H : V n → ℝ) (hH : IsStrictlyStarShapedLevel H) :
    IsCompact (energySurface H) := by
  sorry

end FiniteEnergyPlane
