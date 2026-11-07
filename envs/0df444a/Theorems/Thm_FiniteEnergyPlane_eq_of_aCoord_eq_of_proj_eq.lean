-- Prove2me | Theorems.Thm_FiniteEnergyPlane_eq_of_aCoord_eq_of_proj_eq
-- name    : FiniteEnergyPlane.eq_of_aCoord_eq_of_proj_eq
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-11-06T15:49:32.22324+00:00
-- url     : https://prove2.me/theorems/62c6b791-b1b6-4bb9-a64e-4c7638c8180a
-- title:
--   A nonzero point is determined by its symplectization coordinates
-- statement:
--   Let $H$ be a strictly star-shaped level function on $V_n$. If $x, y \in V_n \setminus \{0\}$ satisfy $a_H(x) = a_H(y)$ and $\mathrm{proj}_H(x) = \mathrm{proj}_H(y)$, then $x = y$.
--
--   **Role.** Injectivity of the coordinates $(a_H, \mathrm{proj}_H)$ on $V_n \setminus \{0\}$.
-- source:
--   Elementary lemma in the setting of U. Hryniewicz, Fast finite-energy planes in symplectizations and applications, Trans. AMS 364 (2012), arXiv:0812.4076

import Definitions.Def_FiniteEnergyPlane_Setting

namespace FiniteEnergyPlane

open MeasureTheory Metric Filter Topology
open scoped ContDiff ENNReal Real

/-- A nonzero point of `V n` is determined by its symplectization coordinates `aCoord H`, `proj H`. -/
theorem eq_of_aCoord_eq_of_proj_eq {n : ℕ} (H : V n → ℝ) (hH : IsStrictlyStarShapedLevel H)
    {x y : V n} (hx : x ≠ 0) (hy : y ≠ 0) (ha : aCoord H x = aCoord H y)
    (hp : proj H x = proj H y) : x = y := by
  sorry

end FiniteEnergyPlane
