-- Prove2me | Theorems.Thm_AvramDividend_Classical_p2m81_bv_root_eventual_psi_above_no_standing_public
-- name    : AvramDividend.Classical.p2m81_bv_root_eventual_psi_above_no_standing_public
-- status  : Open
-- author  : @WillR
-- created : 2026-11-22T04:12:17.406276+00:00
-- url     : https://prove2.me/theorems/7ef18652-de35-41c4-8004-fdea4436737a
-- title:
--   Root-based eventual Laplace growth without standing (public)
-- statement:
--   For a bounded-variation spectrally negative Lévy process with positive discount q and positive Laplace root φ, the Laplace exponent eventually exceeds q, with no Standing assumption. Public bridge replaying the standing eventual-growth proof with root drift.
-- source:
--   Source-faithful replay of Proved AvramDividend.Classical.psi_eventually_gt_of_boundedVariation (e9a8e903-54cb-4709-8fa1-330ae9e496bb, proof b4c15c16-a5f7-42b3-8491-9ddb7b43bee3) with root drift p2m81_bv_root_drift_pos_no_standing_public in place of bv_standing_drift_pos. Uses only otherwise standing-free Proved helpers: bv_small_negative_first_moment_integrable 2296f406, levy_small_negative_compensated_div_integrable e1ef23c7, levy_large_negative_jump_unit_integrable 30dea431, negative_compensated_real_integral_tendsto_finite c02c41f4, negative_compensated_integral_mono 6aaa2254, psi_normalised_lower_bound_small 6952003f. Supplies eventual hψ for scaleFunction_strict_pos_of_eventual_psi_bound 793f3b68 in public parent 33b910b1. No hypotheses weakened.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory Filter Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.p2m81_bv_root_eventual_psi_above_no_standing_public
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q φ : ℝ) (hq : 0 < q) (hφ : 0 < φ) (hroot : X.ψ φ = q)
    (hBV : X.BoundedVariation) :
    ∃ β₀ : ℝ, 0 ≤ β₀ ∧ ∀ θ : ℝ, β₀ ≤ θ → q < X.ψ θ := by sorry
