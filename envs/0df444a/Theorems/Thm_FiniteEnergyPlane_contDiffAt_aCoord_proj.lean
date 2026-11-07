-- Prove2me | Theorems.Thm_FiniteEnergyPlane_contDiffAt_aCoord_proj
-- name    : FiniteEnergyPlane.contDiffAt_aCoord_proj
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-11-06T16:40:26.7922+00:00
-- url     : https://prove2.me/theorems/37c12cd3-f2a3-48ae-b6c1-5b1813363067
-- title:
--   The symplectization coordinates are smooth away from the origin
-- statement:
--   Let $S = H^{-1}(1)$ be a strictly star-shaped level. At every $y \ne 0$ the symplectization coordinates $\mathtt{aCoord}\ H$ and $\mathtt{proj}\ H$ are of class $C^\infty$.
--
--   **Role.** A basic regularity fact about the coordinates $y = e^{2a} x$, $x \in S$, on $\mathbb{R}^{2n+2} \setminus \{0\}$.
-- source:
--   Elementary lemma in the setting of U. Hryniewicz, Fast finite-energy planes in symplectizations and applications, Trans. AMS 364 (2012), arXiv:0812.4076

import Definitions.Def_FiniteEnergyPlane_Setting

namespace FiniteEnergyPlane

open scoped ContDiff

/-- Away from `0`, the symplectization coordinates `aCoord H` and `proj H` are smooth. -/
theorem contDiffAt_aCoord_proj {n : ℕ} (H : V n → ℝ) (hH : IsStrictlyStarShapedLevel H)
    (y : V n) (hy : y ≠ 0) : ContDiffAt ℝ ∞ (aCoord H) y ∧ ContDiffAt ℝ ∞ (proj H) y := by
  sorry

end FiniteEnergyPlane
