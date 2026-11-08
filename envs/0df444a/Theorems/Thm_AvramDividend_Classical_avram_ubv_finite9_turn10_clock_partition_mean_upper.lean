-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ubv_finite9_turn10_clock_partition_mean_upper
-- name    : AvramDividend.Classical.avram_ubv_finite9_turn10_clock_partition_mean_upper
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-07T23:26:02.247076+00:00
-- url     : https://prove2.me/theorems/4e4d8bf2-081e-4e07-aa49-5228a8f5d13a
-- title:
--   Positive-clock conditional stopped reward mean and zero-clock bound imply full expected upper bound
-- statement:
--   For the original stopped discounted reward, the strictly positive-clock event and the zero-clock event partition the probability space. If the reward is integrable, the positive-clock conditional integral is no more than the original benchmark times the event probability, and the time-zero reward is pointwise at most that benchmark, the full expected reward has the same upper bound. Applies to Gaussian, pure-jump, and mixed Lévy branches without altering the source or clock.

import Mathlib

open MeasureTheory Set
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_ubv_finite9_turn10_clock_partition_mean_upper
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P]
    (b : ℝ) (σ : Ω → ℝ≥0) (F : Ω → ℝ)
    (hzeroMeas : MeasurableSet {ω : Ω | σ ω = 0})
    (hFI : Integrable F P)
    (hzero : ∀ ω, σ ω = 0 → F ω ≤ b)
    (hpositive : (∫ ω in {ω : Ω | σ ω ≠ 0}, F ω ∂P) ≤
      b * (P {ω : Ω | σ ω ≠ 0}).toReal) :
    (∫ ω, F ω ∂P) ≤ b := by sorry
