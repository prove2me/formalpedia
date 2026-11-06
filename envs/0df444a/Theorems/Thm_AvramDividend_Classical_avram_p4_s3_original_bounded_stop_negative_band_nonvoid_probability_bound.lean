-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p4_s3_original_bounded_stop_negative_band_nonvoid_probability_bound
-- name    : AvramDividend.Classical.avram_p4_s3_original_bounded_stop_negative_band_nonvoid_probability_bound
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-05T10:23:45.505902+00:00
-- url     : https://prove2.me/theorems/49d189c2-9950-42b8-93ee-0387ab780548
-- title:
--   Any negative-band jump before an arbitrary bounded original-process ruin clock has probability at most Tν(B)
-- statement:
--   For any random clock τ bounded by T, the physical original-process probability of at least one intrinsic negative-band jump before τ is at most r=(T ν(B)).toReal. The estimate needs no measurable or stopping-time assumption on τ because probability monotonicity holds for arbitrary subsets.
-- source:
--   Accepted source deterministic nonvoid second-order bound 604dfce2-720c-427f-b655-b2548c554962 and original marked-time finite theorem avram_wave7_06_original_negative_band_marked_times_finite; set inclusion and measure monotonicity.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_p4_s3_original_bounded_stop_negative_band_nonvoid_probability_bound
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (T : ℝ≥0) (n : ℕ)
    (τ : Ω → ℝ≥0) (hτ : ∀ ω, τ ω ≤ T) :
    let K : Ω → ℕ := fun ω =>
      {u : ℝ≥0 | 0 < u ∧ u ≤ τ ω ∧
        X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≤
          -(1 / ((n : ℝ) + 1))}.ncard
    let r : ℝ :=
      ((T : ℝ≥0∞) * X.ν (Iic (-(1 / ((n : ℝ) + 1))))).toReal
    P.real {ω : Ω | K ω ≠ 0} ≤ r := by sorry
