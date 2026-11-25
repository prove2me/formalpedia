-- Prove2me | Theorems.Thm_FiniteEnergyPlane_isPathConnected_energySurface_diff_range
-- name    : FiniteEnergyPlane.isPathConnected_energySurface_diff_range
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-11-25T12:12:30.311283+00:00
-- url     : https://prove2.me/theorems/cf2ff696-bf82-59d9-824b-ec7020e512db
-- title:
--   The complement of a curve in a star-shaped level is path connected
-- statement:
--   Let $S=H^{-1}(1)\subset\mathbb{R}^{2n+2}$ be a strictly star-shaped level. If $n\ge1$ and $x:\mathbb{R}\to S$ is a $C^1$ curve, then $S\setminus x(\mathbb{R})$ is path connected.
--
--   Reusable for knot and link complements in star-shaped levels, for example complements of periodic orbits.
-- source:
--   U. Hryniewicz, Fast finite-energy planes in symplectizations and applications, Trans. Amer. Math. Soc. 364 (2012), 1859-1931, arXiv:0812.4076, Section 7

import Definitions.Def_FiniteEnergyPlane_OpenBook

namespace FiniteEnergyPlane

open MeasureTheory Metric Filter Topology
open scoped ContDiff ENNReal Real

/-- The complement of a `C¹` curve in a star-shaped level of dimension at least three is path connected. -/
theorem isPathConnected_energySurface_diff_range {n : ℕ} (hn : 1 ≤ n) (H : V n → ℝ)
    (hH : IsStrictlyStarShapedLevel H) (x : ℝ → V n) (hx : ContDiff ℝ 1 x)
    (hxS : ∀ t, x t ∈ energySurface H) :
    IsPathConnected (energySurface H \ Set.range x) := by
  sorry

end FiniteEnergyPlane
