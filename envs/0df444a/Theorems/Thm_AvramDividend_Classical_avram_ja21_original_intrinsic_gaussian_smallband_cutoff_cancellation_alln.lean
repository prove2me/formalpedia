-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ja21_original_intrinsic_gaussian_smallband_cutoff_cancellation_alln
-- name    : AvramDividend.Classical.avram_ja21_original_intrinsic_gaussian_smallband_cutoff_cancellation_alln
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-21T14:32:29.171281+00:00
-- url     : https://prove2.me/theorems/821edc3f-2a77-4c4e-b4a4-a6326e6e979e
-- title:
--   Exact intrinsic cutoff cancellation: Gaussian truncated residual plus retained compensated small jumps equals X minus drift and large jumps
-- statement:
--   The original truncated residual equals the genuine original Lévy path minus triplet drift minus the retained compensated small negative marks minus large-mark jump sum. Adding back the identical retained compensated small marks cancels exactly for every cutoff n and time t. This algebraic identity exposes why an earlier theorem wrongly omitted small-jump variance in its purported Gaussian-only cutoff-zero second moment.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_truncated_residual
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_small_band_compensated
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_large_jump_sum
set_option autoImplicit false
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_ja21_original_intrinsic_gaussian_smallband_cutoff_cancellation_alln
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (n : ℕ)
    (t : ℝ≥0) (ω : Ω) :
    avram_p4_h_gaussian_intrinsic_truncated_residual X n t ω +
      avram_p4_h_gaussian_intrinsic_small_band_compensated X n t ω =
    X.X t ω - (t : ℝ) * X.c -
      avram_p4_h_gaussian_intrinsic_large_jump_sum X t ω := by sorry
