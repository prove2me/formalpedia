-- Prove2me | Theorems.Thm_FiniteEnergyPlane_loopAction_ccwLoop_eq_dlambdaEnergy
-- name    : FiniteEnergyPlane.loopAction_ccwLoop_eq_dlambdaEnergy
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-10-25T21:14:19.175197+00:00
-- url     : https://prove2.me/theorems/090f7da0-7e2a-4d50-9fb8-ea66d7a29724
-- title:
--   Action of a large circle equals the enclosed dλ-energy of a finite-energy plane
-- statement:
--   Let $S=H^{-1}(1)\subset\mathbb R^{2n+2}$ be a strictly star-shaped level and $J$ a smooth $d\lambda_0$-compatible complex structure on $\xi$, with associated almost complex structure $\tilde J$. Let $u:\mathbb C\to\mathbb R^{2n+2}\setminus\{0\}$ be a finite-energy $\tilde J$-holomorphic plane and $R>0$. Then the action of the counterclockwise loop $\gamma_R(t)=\mathrm{proj}\,u(Re^{2\pi it})$ equals the $d\lambda$-energy of $u$ on the disc $B(0,R)$:
--   $$\int_0^1\lambda_0\big(\gamma_R(t)\big)\big(\gamma_R'(t)\big)\,dt\;=\;\int_{B(0,R)}u^*d\lambda .$$
--
--   **Formalization Note** The left side is `loopAction H u (ccwLoop R)`, where $\mathrm{proj}$ is the radial projection `proj H` onto $S$. The right side is `dlambdaEnergy H (ball 0 R) u`, an element of $[0,\infty]$, converted with `toReal` (its value is finite here).
-- source:
--   H. Hofer, Pseudoholomorphic curves in symplectizations with applications to the Weinstein conjecture in dimension three, Invent. Math. 114 (1993), 515–563, proof of Theorem 31, p. 537

import Definitions.Def_FiniteEnergyPlane_Setting

namespace FiniteEnergyPlane

open MeasureTheory Metric Filter Topology
open scoped ContDiff ENNReal Real

/-- Action of a circle equals the enclosed `dλ`-energy (Hofer 1993, p. 537). For a finite-energy
`J̃`-holomorphic plane `u` and `R > 0`, the action of the counterclockwise loop
`t ↦ proj(u(R e^{2π i t}))` equals the `dλ`-energy `∫_{B(0,R)} u*dλ` of `u` on the disc `B(0, R)`. -/
theorem loopAction_ccwLoop_eq_dlambdaEnergy {n : ℕ} (H : V n → ℝ)
    (hH : IsStrictlyStarShapedLevel H) (J : V n → V n →L[ℝ] V n)
    (hJ : IsCompatibleXiStructure H J) (u : ℂ → V n) (hu : IsFiniteEnergyCurve H J Set.univ u)
    (R : ℝ) (hR : 0 < R) :
    loopAction H u (ccwLoop R) = (dlambdaEnergy H (ball 0 R) u).toReal := by
  sorry

end FiniteEnergyPlane
