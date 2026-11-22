-- Prove2me | Theorems.Thm_FiniteEnergyPlane_dlambdaEnergy_norm_sub_gt_eq_sub
-- name    : FiniteEnergyPlane.dlambdaEnergy_norm_sub_gt_eq_sub
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-11-22T19:45:29.7937+00:00
-- url     : https://prove2.me/theorems/3d1b0427-4a5a-4ac3-8d35-6cdd40d379a4
-- title:
--   The dλ-energy outside a disc is the total energy minus the energy of the disc
-- statement:
--   Let $H$ define a level $S=H^{-1}(1)\subset\mathbb{R}^{2n+2}$ and let $u:\mathbb{C}\to\mathbb{R}^{2n+2}$ have total $d\lambda$-energy equal to a real number $T$. Then for every $\zeta\in\mathbb{C}$ and $\rho\in\mathbb{R}$,
--   $$\int_{\{|x-\zeta|>\rho\}}u^*d\lambda \;=\; T-\int_{B_\rho(\zeta)}u^*d\lambda .$$
--
--   It converts the energy normalization of a plane outside a disc into a condition on the energy of the disc.
--
--   **Formalization Note** The $d\lambda$-energy on $A$ is `dlambdaEnergy H A u` in `ℝ≥0∞`, so the subtraction is truncated subtraction in `ℝ≥0∞`; $B_\rho(\zeta)$ is `Metric.ball ζ ρ` and the outside is `{x | ρ < ‖x - ζ‖}`.
-- source:
--   Elementary (dλ-energy bookkeeping), used for Hryniewicz (2012), Lemma 7.3

import Definitions.Def_FiniteEnergyPlane_Setting

namespace FiniteEnergyPlane

open MeasureTheory Metric Filter Topology
open scoped ContDiff ENNReal Real

/-- If the total `dλ`-energy of `u : ℂ → V n` is `T`, then its `dλ`-energy outside the closed disc
`{‖x - ζ‖ ≤ ρ}` is `T` minus its `dλ`-energy on the open disc `B_ρ(ζ)`. -/
theorem dlambdaEnergy_norm_sub_gt_eq_sub {n : ℕ} (H : V n → ℝ) (u : ℂ → V n) (T : ℝ)
    (htot : dlambdaEnergy H Set.univ u = ENNReal.ofReal T) (ζ : ℂ) (ρ : ℝ) :
    dlambdaEnergy H {x | ρ < ‖x - ζ‖} u = ENNReal.ofReal T - dlambdaEnergy H (ball ζ ρ) u := by
  sorry

end FiniteEnergyPlane
