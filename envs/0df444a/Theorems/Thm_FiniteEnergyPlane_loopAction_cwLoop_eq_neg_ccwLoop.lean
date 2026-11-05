-- Prove2me | Theorems.Thm_FiniteEnergyPlane_loopAction_cwLoop_eq_neg_ccwLoop
-- name    : FiniteEnergyPlane.loopAction_cwLoop_eq_neg_ccwLoop
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-11-04T17:09:41.192958+00:00
-- url     : https://prove2.me/theorems/37381136-a9af-48ab-8127-71bccda1b033
-- title:
--   The clockwise and counterclockwise actions of a circle are opposite
-- statement:
--   Let $u:\mathbb{C}\to\mathbb{R}^{2n+2}$ be such that $\mathrm{proj}\circ u$ is smooth on an open set containing the circle $|z|=\rho$. Then the action of the clockwise loop $t\mapsto\mathrm{proj}(u(\rho e^{-2\pi it}))$ is minus the action of the counterclockwise loop $t\mapsto\mathrm{proj}(u(\rho e^{2\pi it}))$.
-- source:
--   U. Hryniewicz, Fast finite-energy planes in symplectizations and applications, Trans. Amer. Math. Soc. 364 (2012), 1859-1931, Lemma 4.11; H. Hofer, K. Wysocki, E. Zehnder, Finite energy cylinders of small area, Ergodic Theory Dynam. Systems 22 (2002), 1451-1486, Theorem 1.1

import Definitions.Def_FiniteEnergyPlane_Setting
import Mathlib.Analysis.SpecialFunctions.Complex.CircleMap

namespace FiniteEnergyPlane

open MeasureTheory Metric Filter Topology
open scoped ContDiff ENNReal Real

/-- If `proj ∘ u` is smooth on an open set containing the circle of radius `ρ` about `0`, the action
of the clockwise loop is minus the action of the counterclockwise loop. -/
theorem loopAction_cwLoop_eq_neg_ccwLoop {n : ℕ} (H : V n → ℝ) (u : ℂ → V n) {U : Set ℂ}
    (hU : IsOpen U) (hw : ContDiffOn ℝ ∞ (fun z => proj H (u z)) U) (ρ : ℝ)
    (hρ : ∀ θ, circleMap 0 ρ θ ∈ U) :
    loopAction H u (cwLoop 0 ρ) = -loopAction H u (ccwLoop ρ) := by
  sorry

end FiniteEnergyPlane
