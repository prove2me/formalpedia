-- Prove2me | Theorems.Thm_FiniteEnergyPlane_exists_lipschitzOnWith_reeb
-- name    : FiniteEnergyPlane.exists_lipschitzOnWith_reeb
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-11-04T16:08:35.110337+00:00
-- url     : https://prove2.me/theorems/53efa90e-6d70-44ae-bacd-ef8b3f7cd4a5
-- title:
--   The Reeb field of a star-shaped level is Lipschitz on the level
-- statement:
--   Let $S=H^{-1}(1)\subset\mathbb{R}^{2n+2}$ be a strictly star-shaped level with Reeb field $R$. Then there is $K\ge 0$ such that $\|R(x)-R(y)\|\le K\|x-y\|$ for all $x,y\in S$.
-- source:
--   U. Hryniewicz, Fast finite-energy planes in symplectizations and applications, Trans. Amer. Math. Soc. 364 (2012), 1859-1931, § 4.4

import Definitions.Def_FiniteEnergyPlane_Setting

namespace FiniteEnergyPlane

open MeasureTheory Metric Filter Topology
open scoped ContDiff ENNReal Real

/-- The Reeb field of a strictly star-shaped level `S` is Lipschitz on `S`. -/
theorem exists_lipschitzOnWith_reeb {n : ℕ} (H : V n → ℝ) (hH : IsStrictlyStarShapedLevel H) :
    ∃ K : NNReal, LipschitzOnWith K (reeb H) (energySurface H) := by
  sorry

end FiniteEnergyPlane
