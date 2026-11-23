-- Prove2me | Theorems.Thm_FiniteEnergyPlane_pos_of_hasDerivAt_dlambdaEnergy_ball
-- name    : FiniteEnergyPlane.pos_of_hasDerivAt_dlambdaEnergy_ball
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-11-22T19:27:13.425863+00:00
-- url     : https://prove2.me/theorems/15bed673-a52c-4f94-818e-b9ff4da8f3d1
-- title:
--   The dλ-energy of a fast plane on discs grows strictly in the radius
-- statement:
--   Let $S=H^{-1}(1)\subset\mathbb{R}^4$ be a strictly star-shaped level, $J$ a $d\lambda_0$-compatible complex structure on $\xi$ and $u$ a fast finite-energy plane. Let $\zeta\in\mathbb{C}$ and $\rho>0$. If the function $s\mapsto\int_{B_s(\zeta)}u^*d\lambda$ is differentiable at $\rho$ with derivative $d$, then $d>0$.
--
--   It is used to solve for the radius that fixes the energy normalization of a plane.
--
--   **Formalization Note** The energy on the disc is `(dlambdaEnergy H (Metric.ball ζ s) u).toReal`; differentiability with derivative $d$ is `HasDerivAt`. "Fast finite-energy plane" is `IsFastPlane H J u`.
-- source:
--   U. Hryniewicz, Fast finite-energy planes in symplectizations and applications, Trans. Amer. Math. Soc. 364 (2012), 1859-1931, arXiv:0812.4076, Section 7.1

import Definitions.Def_FiniteEnergyPlane_Winding

namespace FiniteEnergyPlane

open MeasureTheory Metric Filter Topology
open scoped ContDiff ENNReal Real

/-- The `dλ`-energy of a fast finite-energy plane on discs grows at a positive rate in the radius:
if `ρ ↦ E_{dλ}(u; B_ρ(ζ))` has derivative `d` at `ρ > 0`, then `d > 0`. -/
theorem pos_of_hasDerivAt_dlambdaEnergy_ball (H : V 1 → ℝ) (hH : IsStrictlyStarShapedLevel H)
    (J : V 1 → V 1 →L[ℝ] V 1) (hJ : IsCompatibleXiStructure H J) (u : ℂ → V 1)
    (hu : IsFastPlane H J u) (ζ : ℂ) (ρ : ℝ) (hρ : 0 < ρ) (d : ℝ)
    (hd : HasDerivAt (fun s => (dlambdaEnergy H (ball ζ s) u).toReal) d ρ) : 0 < d := by
  sorry

end FiniteEnergyPlane
