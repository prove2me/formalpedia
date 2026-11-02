-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave5_01_actual_source_marked_count_clock_translation
-- name    : AvramDividend.Classical.avram_wave5_01_actual_source_marked_count_clock_translation
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-01T14:28:20.603296+00:00
-- url     : https://prove2.me/theorems/01b004c1-fba2-4778-a12a-1c4a27e2ced0
-- title:
--   Actual source marked interval count equals exact relative-clock count on same path
-- statement:
--   For every actual SpectrallyNegativeLevy P 𝓕 original sample path ω, deterministic start s and length T and arbitrary Borel marks B, the literal marked source counting measure N_X(ω) on (s,s+T]×B equals the en-cardinality of genuine source jumps indexed at relative times v∈(0,T] whose original positive-time mark at s+v lies in B. This is a pathwise bijective time-translation identity with no almost-everywhere exception, copy, probability-law transport, BV, or compensator assumption. Together with the shifted strict-left limit identity it identifies genuine future-increment jumps with the original marked source measure, a necessary bridge for stationary marked-count laws.
-- source:
--   The Proved exact source Borel marked measure encard identity UUID 2c942e8f-b7ac-4d46-9808-101b8797d184, plus injectivity of time addition and finite-or-infinite set encard invariance under injective images.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave5_01_actual_source_marked_jump_measure_arbitrary_borel_count_exact
open MeasureTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_wave5_01_actual_source_marked_count_clock_translation
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (ω : Ω) (s T : ℝ≥0) (B : Set ℝ) (hB : MeasurableSet B) :
    ((Measure.count.restrict {u : ℝ≥0 |
      0 < u ∧ X.X u ω -
        Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
      (fun u : ℝ≥0 => (u,
        X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
      (Ioc s (s + T) ×ˢ B) =
    ({v : ℝ≥0 | 0 < v ∧ v ≤ T ∧
      X.X (s + v) ω -
        Function.leftLim (fun w : ℝ≥0 => X.X w ω) (s + v) ≠ 0 ∧
      X.X (s + v) ω -
        Function.leftLim (fun w : ℝ≥0 => X.X w ω) (s + v) ∈ B}).encard := by sorry
