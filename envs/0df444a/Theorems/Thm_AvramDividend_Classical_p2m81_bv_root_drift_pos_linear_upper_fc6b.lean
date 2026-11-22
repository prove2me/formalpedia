-- Prove2me | Theorems.Thm_AvramDividend_Classical_p2m81_bv_root_drift_pos_linear_upper_fc6b
-- name    : AvramDividend.Classical.p2m81_bv_root_drift_pos_linear_upper_fc6b
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-22T09:34:27.373005+00:00
-- url     : https://prove2.me/theorems/923542c0-f151-4b48-8975-b2425cd18231
-- title:
--   BV root drift positivity and linear Laplace upper bound
-- statement:
--   For BV spectrally negative Levy with positive q and root phi where psi phi equals q, the drift is positive and psi theta is at most drift times theta for all nonnegative theta. Helper M1 for parent fc6b315a: linear upper from psi_upper_bound_by_compensated_small_jumps plus compensated-jump integrability helpers gives drift positivity from the root; feeds the Tauberian lower-bound contradiction.
-- source:
--   Decomposition child M1 of fc6b315a standing-free scale-origin route (249-line proof exceeds 100-line/2500-token/complexity caps). Proved from psi_upper_bound_by_compensated_small_jumps, levy_compensated_jump_integrable_nonneg and bv_small_negative_first_moment_integrable with BV sigma-zero simplification.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.p2m81_bv_root_drift_pos_linear_upper_fc6b
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q φ : ℝ) (hq : 0 < q) (hφ : 0 < φ) (hroot : X.ψ φ = q)
    (hBV : X.BoundedVariation) :
    0 < X.drift ∧ ∀ θ : ℝ, 0 ≤ θ → X.ψ θ ≤ X.drift * θ := by sorry
