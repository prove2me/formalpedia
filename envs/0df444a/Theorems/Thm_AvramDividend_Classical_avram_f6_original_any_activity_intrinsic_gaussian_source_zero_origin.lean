-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_f6_original_any_activity_intrinsic_gaussian_source_zero_origin
-- name    : AvramDividend.Classical.avram_f6_original_any_activity_intrinsic_gaussian_source_zero_origin
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-18T20:38:57.419978+00:00
-- url     : https://prove2.me/theorems/eb8e9ad9-8b40-427b-b982-eb2c481a6e4b
-- title:
--   Original arbitrary-activity Gaussian intrinsic cutoff almost-sure limit vanishes at zero
-- statement:
--   For any genuine spectrally negative Lévy process, including both finite and infinite negative-jump activity, and any a.e.-defined pathwise limit of its actual intrinsic Gaussian truncated residual approximations at each time, the limit at clock zero is zero almost surely. Uses only the Proved pointwise source formula that every true original Gaussian residual cutoff vanishes at time zero and uniqueness of limits in ℝ. No auxiliary small-jump martingale limit or standing finite-activity assumption is required, strengthening the previously proved paired-origin conclusion. Useful as a verified zero-initial-condition for original stopped Gaussian Itô martingale terms.
-- source:
--   Proved 2e39b05b original intrinsic truncated residual at zero for every cutoff.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_truncated_residual
open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_f6_original_any_activity_intrinsic_gaussian_source_zero_origin
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (R : ℝ≥0 → Ω → ℝ)
    (hR : ∀ᵐ ω ∂P, ∀ t : ℝ≥0,
      Tendsto (fun k : ℕ =>
        avram_p4_h_gaussian_intrinsic_truncated_residual X k t ω)
        atTop (nhds (R t ω))) :
    ∀ᵐ ω ∂P, R 0 ω = 0 := by sorry
