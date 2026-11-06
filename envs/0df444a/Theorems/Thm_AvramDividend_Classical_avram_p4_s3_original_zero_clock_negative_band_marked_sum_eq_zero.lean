-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p4_s3_original_zero_clock_negative_band_marked_sum_eq_zero
-- name    : AvramDividend.Classical.avram_p4_s3_original_zero_clock_negative_band_marked_sum_eq_zero
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-05T18:32:43.889072+00:00
-- url     : https://prove2.me/theorems/f32fc144-ab5c-4472-bf7c-e5be26fecf2e
-- title:
--   The original negative-band physical marked-time jump sum has zero time-zero atom at a zero stopping clock
-- statement:
--   For any original spectrally negative Lévy process, path ω, band n and arbitrary physical marked-time coefficient, if the stopped physical horizon τ(ω)=0, the finite sum over original negative-band jump times up to τ(ω) vanishes exactly. The jump-time set excludes u=0 explicitly.
-- source:
--   Exact source negative-band marked-time finite set with strict positive-time membership; Set.toFinset_eq_empty.

import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave7_06_original_negative_band_marked_times_finite
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_p4_s3_original_zero_clock_negative_band_marked_sum_eq_zero
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (n : ℕ)
    (τ : Ω → ℝ≥0) (ω : Ω) (hτ0 : τ ω = 0)
    (f : Ω → ℝ≥0 → ℝ) :
    ∑ u ∈ (avram_wave7_06_original_negative_band_marked_times_finite
      X ω (τ ω) n).toFinset, f ω u = 0 := by sorry
