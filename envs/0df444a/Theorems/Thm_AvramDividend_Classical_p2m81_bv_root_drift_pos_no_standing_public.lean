-- Prove2me | Theorems.Thm_AvramDividend_Classical_p2m81_bv_root_drift_pos_no_standing_public
-- name    : AvramDividend.Classical.p2m81_bv_root_drift_pos_no_standing_public
-- status  : Open
-- author  : @WillR
-- created : 2026-11-22T04:12:13.076808+00:00
-- url     : https://prove2.me/theorems/e7c8659d-b1f4-46bd-97ab-5ed4dbb4ba78
-- title:
--   Root-based drift positivity without standing (public)
-- statement:
--   For a bounded-variation spectrally negative Lévy process with positive discount q and positive Laplace root φ, the drift is strictly positive, with no Standing assumption. Public bridge isolating q ≤ φ·drift from the BV Laplace upper bound.
-- source:
--   Source-faithful extraction from public parent AvramDividend.Classical.p2m81_bv_root_scale_pos_no_standing_public (33b910b1-d802-435b-8b3a-4c5717e7a258) draft /tmp/p2m81_childB_scalepos_proof.lean drift block. Proves q=ψφ ≤ φ·drift via psi_upper_bound_by_compensated_small_jumps 85d8b8ec, bv_small_negative_first_moment_integrable 2296f406, levy_compensated_jump_integrable_nonneg 1f95f376, and exp(φy)-1≤0 for y<0. Replaces bv_standing_drift_pos in the replay of psi_eventually_gt_of_boundedVariation e9a8e903. No hypotheses weakened.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory Filter Set Topology
open AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.p2m81_bv_root_drift_pos_no_standing_public
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q φ : ℝ) (hq : 0 < q) (hφ : 0 < φ) (hroot : X.ψ φ = q)
    (hBV : X.BoundedVariation) :
    0 < X.drift := by sorry
