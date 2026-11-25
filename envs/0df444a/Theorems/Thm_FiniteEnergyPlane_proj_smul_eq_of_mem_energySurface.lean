-- Prove2me | Theorems.Thm_FiniteEnergyPlane_proj_smul_eq_of_mem_energySurface
-- name    : FiniteEnergyPlane.proj_smul_eq_of_mem_energySurface
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-11-25T11:52:19.669963+00:00
-- url     : https://prove2.me/theorems/576034b4-d7ca-5656-83dc-95d6e859c7b0
-- title:
--   The radial projection on rays through points of the level
-- statement:
--   Let $S=H^{-1}(1)\subset\mathbb{R}^{2n+2}$ be a strictly star-shaped level. If $x\in S$ and $r>0$ then the radial projection of $rx$ is $x$.
--
--   Basic fact about the radial projection, reusable throughout the symplectization setting.
-- source:
--   U. Hryniewicz, Fast finite-energy planes in symplectizations and applications, Trans. Amer. Math. Soc. 364 (2012), 1859-1931, arXiv:0812.4076, Section 7

import Definitions.Def_FiniteEnergyPlane_OpenBook

namespace FiniteEnergyPlane

open MeasureTheory Metric Filter Topology
open scoped ContDiff ENNReal Real

/-- The radial projection of a positive multiple of a point of `S` is that point. -/
theorem proj_smul_eq_of_mem_energySurface {n : ℕ} (H : V n → ℝ)
    (hH : IsStrictlyStarShapedLevel H) (x : V n) (hx : x ∈ energySurface H) (r : ℝ) (hr : 0 < r) :
    proj H (r • x) = x := by
  sorry

end FiniteEnergyPlane
