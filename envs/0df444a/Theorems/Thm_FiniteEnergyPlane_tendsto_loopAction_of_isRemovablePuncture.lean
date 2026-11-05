-- Prove2me | Theorems.Thm_FiniteEnergyPlane_tendsto_loopAction_of_isRemovablePuncture
-- name    : FiniteEnergyPlane.tendsto_loopAction_of_isRemovablePuncture
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-11-04T17:09:38.333177+00:00
-- url     : https://prove2.me/theorems/7ec8e6d5-e7f3-4ae4-8adf-99976e529b10
-- title:
--   At a removable puncture the loop actions tend to zero
-- statement:
--   Let $S=H^{-1}(1)$ be a strictly star-shaped level and let the puncture $0$ of $u$ on the punctured unit disc be removable. Then the actions of the clockwise loops $t\mapsto\mathrm{proj}(u(\rho e^{-2\pi it}))$ tend to $0$ as $\rho\to0^+$.
-- source:
--   U. Hryniewicz, Fast finite-energy planes in symplectizations and applications, Trans. Amer. Math. Soc. 364 (2012), 1859-1931, Lemma 4.11; H. Hofer, K. Wysocki, E. Zehnder, Finite energy cylinders of small area, Ergodic Theory Dynam. Systems 22 (2002), 1451-1486, Theorem 1.1

import Definitions.Def_FiniteEnergyPlane_Setting

namespace FiniteEnergyPlane

open MeasureTheory Metric Filter Topology
open scoped ContDiff ENNReal Real

/-- At a removable puncture `0` of `u` on the punctured unit disc, the actions of the clockwise
circles of radius `ρ` tend to `0` as `ρ → 0⁺`. -/
theorem tendsto_loopAction_of_isRemovablePuncture {n : ℕ} (H : V n → ℝ) (hH : IsStrictlyStarShapedLevel H)
    (J : V n → V n →L[ℝ] V n) (hJ : IsCompatibleXiStructure H J) (u : ℂ → V n)
    (hrem : IsRemovablePuncture H J u 0 1) :
    Tendsto (fun ρ => loopAction H u (cwLoop 0 ρ)) (𝓝[>] 0) (𝓝 0) := by
  sorry

end FiniteEnergyPlane
