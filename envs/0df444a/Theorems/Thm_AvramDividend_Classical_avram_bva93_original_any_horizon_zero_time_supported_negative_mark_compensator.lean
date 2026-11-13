-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bva93_original_any_horizon_zero_time_supported_negative_mark_compensator
-- name    : AvramDividend.Classical.avram_bva93_original_any_horizon_zero_time_supported_negative_mark_compensator
-- status  : Open
-- author  : @WillR
-- created : 2026-11-12T21:56:16.677139+00:00
-- url     : https://prove2.me/theorems/e3b8f306-33f1-4a50-a72a-e8ffab0623cf
-- title:
--   Original signed negative-mark compensator integral of a zero-time supported kernel vanishes at every horizon
-- statement:
--   At every original nonnegative horizon S, the exact spectrally negative Lévy negative-mark kernel compensator integrated in marks and original mapped real Lebesgue time is zero whenever the stopped kernel is supported at time zero. Proved BVA92 eliminates outer time integral after the inner negative-mark integral vanishes at every positive time. Needed for proving the original M_n(S)=0 pathwise under ruinTime=0, for all S, not merely M_n(0)=0.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open Classical MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

theorem AvramDividend.Classical.avram_bva93_original_any_horizon_zero_time_supported_negative_mark_compensator
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (H : ((ℝ≥0 × Ω) × ℝ) → ℝ) (ω : Ω) (S : ℝ≥0)
    (hSupport : ∀ (t : ℝ≥0), t ≠ 0 → ∀ z : ℝ, H ((t, ω), z) = 0) :
    (∫ t, ∫ z, H ((t, ω), z) ∂(X.ν.restrict (Iio (0 : ℝ)))
      ∂(((volume : Measure ℝ).restrict (Icc 0 (S : ℝ))).map Real.toNNReal)) = 0 := by sorry
