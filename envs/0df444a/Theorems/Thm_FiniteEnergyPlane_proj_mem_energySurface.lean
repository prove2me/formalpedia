-- Prove2me | Theorems.Thm_FiniteEnergyPlane_proj_mem_energySurface
-- name    : FiniteEnergyPlane.proj_mem_energySurface
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-11-25T11:37:26.992015+00:00
-- url     : https://prove2.me/theorems/c9278e11-f5b0-5419-9fe6-5c68b241ad5e
-- title:
--   The radial projection to a star-shaped level
-- statement:
--   Let $S=H^{-1}(1)\subset\mathbb{R}^{2n+2}$ be a strictly star-shaped level. The radial projection of every $y\ne0$ lies in $S$.
--
--   Basic fact about the radial projection, reusable throughout the symplectization setting.
-- source:
--   U. Hryniewicz, Fast finite-energy planes in symplectizations and applications, Trans. Amer. Math. Soc. 364 (2012), 1859-1931, arXiv:0812.4076, Section 7

import Definitions.Def_FiniteEnergyPlane_OpenBook

namespace FiniteEnergyPlane

open MeasureTheory Metric Filter Topology
open scoped ContDiff ENNReal Real

/-- The radial projection takes values in `S`. -/
theorem proj_mem_energySurface {n : ℕ} (H : V n → ℝ) (hH : IsStrictlyStarShapedLevel H) (y : V n)
    (hy : y ≠ 0) : proj H y ∈ energySurface H := by
  sorry

end FiniteEnergyPlane
