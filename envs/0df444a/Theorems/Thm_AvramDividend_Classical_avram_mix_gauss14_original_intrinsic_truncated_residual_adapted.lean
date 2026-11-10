-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_mix_gauss14_original_intrinsic_truncated_residual_adapted
-- name    : AvramDividend.Classical.avram_mix_gauss14_original_intrinsic_truncated_residual_adapted
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-09T10:53:29.451272+00:00
-- url     : https://prove2.me/theorems/42ada2ca-e558-4e25-8ea9-d5528226f47c
-- title:
--   Every original same-space finite-cutoff Gaussian residual is adapted to the physical filtration
-- statement:
--   At every deterministic physical horizon and every cutoff, establish exact original-filtration measurability of the original X Gaussian intrinsic residual. Use the original X adaptedness field and the established Borel negative-band adaptedness for the exact small jump window (-1,-1/(n+1)] and large jump window (-infinity,-1], plus deterministic drift and compensator. This supplies the missing hCut for the Proved a70e016c Gaussian compact-uniform residual limit adaptation theorem, without an auxiliary Brownian or false arbitrary stopping-time-floor assumption.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_truncated_residual
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_small_band_compensated
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_large_jump_sum
import Theorems.Thm_AvramDividend_Classical_avram_mix_gauss14_original_negative_band_integral_adapted
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_mix_gauss14_original_intrinsic_truncated_residual_adapted
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (n : ℕ) (T : ℝ≥0) :
    Measurable[𝓕 T] (fun ω : Ω =>
      avram_p4_h_gaussian_intrinsic_truncated_residual X n T ω) := by sorry
