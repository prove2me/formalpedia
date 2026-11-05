-- Prove2me | Theorems.Thm_FiniteEnergyPlane_loopAction_add_ccwLoop_eq_dlambdaEnergy
-- name    : FiniteEnergyPlane.loopAction_add_ccwLoop_eq_dlambdaEnergy
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-11-04T22:27:57.043933+00:00
-- url     : https://prove2.me/theorems/51361ac0-d012-4ca3-8555-8f2fda86b838
-- title:
--   Action of a finite-energy plane on any circle equals the $d\lambda$-energy of its disk
-- statement:
--   Let $u$ be a finite-energy $\tilde J$-holomorphic plane in the symplectization of a strictly star-shaped level $S\subset\mathbb{R}^{2n+2}$. For every $z_0\in\mathbb{C}$ and $\rho>0$,
--   $$\int_{\partial B_\rho(z_0)}u^*\lambda=\int_{B_\rho(z_0)}u^*d\lambda.$$
--
--   This extends the published identity for disks centered at the origin to arbitrary centers.
--
--   **Formalization Note** The left side is `loopAction H u (fun t => z₀ + ccwLoop ρ t)`, the right side is `(dlambdaEnergy H (ball z₀ ρ) u).toReal`.
-- source:
--   Auxiliary to U. Hryniewicz, Trans. AMS 364 (2012), arXiv:0812.4076, Section 4

import Definitions.Def_FiniteEnergyPlane_Setting

namespace FiniteEnergyPlane

open MeasureTheory Metric Filter Topology
open scoped ContDiff ENNReal Real

/-- For a finite-energy `J̃`-holomorphic plane `u`, the action of `u` along the counterclockwise circle
of radius `ρ` about any center `z₀` equals the `dλ`-energy of `u` on the disk of radius `ρ` about `z₀`. -/
theorem loopAction_add_ccwLoop_eq_dlambdaEnergy {n : ℕ} (H : V n → ℝ)
    (hH : IsStrictlyStarShapedLevel H) (J : V n → V n →L[ℝ] V n) (hJ : IsCompatibleXiStructure H J)
    (u : ℂ → V n) (hu : IsFiniteEnergyCurve H J Set.univ u) (z₀ : ℂ) (ρ : ℝ) (hρ : 0 < ρ) :
    loopAction H u (fun t => z₀ + ccwLoop ρ t) = (dlambdaEnergy H (ball z₀ ρ) u).toReal := by
  sorry

end FiniteEnergyPlane
