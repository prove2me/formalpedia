-- Prove2me | Theorems.Thm_FiniteEnergyPlane_continuous_aCoord_proj_comp
-- name    : FiniteEnergyPlane.continuous_aCoord_proj_comp
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-11-06T15:50:06.685418+00:00
-- url     : https://prove2.me/theorems/a2387640-9d91-4eaf-b044-ed2d79f861f6
-- title:
--   Continuity of the symplectization coordinates of a map
-- statement:
--   Let $H$ be a strictly star-shaped level function on $V_n$ and let $u : \mathbb{C} \to V_n$ be continuous with $u(z) \neq 0$ for all $z$. Then $z \mapsto a_H(u(z))$ and $z \mapsto \mathrm{proj}_H(u(z))$ are continuous.
--
--   **Role.** Basic regularity used whenever a plane is read in the coordinates of the symplectization.
-- source:
--   Elementary lemma in the setting of U. Hryniewicz, Fast finite-energy planes in symplectizations and applications, Trans. AMS 364 (2012), arXiv:0812.4076

import Definitions.Def_FiniteEnergyPlane_Setting

namespace FiniteEnergyPlane

open MeasureTheory Metric Filter Topology
open scoped ContDiff ENNReal Real

/-- The symplectization coordinates of a continuous map avoiding `0` are continuous. -/
theorem continuous_aCoord_proj_comp {n : ℕ} (H : V n → ℝ) (hH : IsStrictlyStarShapedLevel H)
    (u : ℂ → V n) (hu0 : ∀ z, u z ≠ 0) (huc : Continuous u) :
    Continuous (fun z => aCoord H (u z)) ∧ Continuous (fun z => proj H (u z)) := by
  sorry

end FiniteEnergyPlane
