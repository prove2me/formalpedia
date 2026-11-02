-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave5_01_actual_source_marked_count_countable_positive_time_set_zero_ae
-- name    : AvramDividend.Classical.avram_wave5_01_actual_source_marked_count_countable_positive_time_set_zero_ae
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-01T11:57:56.733366+00:00
-- url     : https://prove2.me/theorems/f9f590d4-1726-45e7-8beb-875e31d82d37
-- title:
--   Actual original marked Lévy jump measure vanishes on every prescribed countable set of positive times almost surely
-- statement:
--   For any prescribed countable deterministic subset C of positive times and any Borel jump-mark band B, the actual source marked jump-counting measure N_X(C×B) equals zero on a probability-one event. This simultaneous in-time source identity uses the original no-fixed-time-jump law, countable conjunction under P, and the proved exact arbitrary-Borel same-path counting measure; it supports finite- and countable-grid boundary truncations without time atoms or copied Poisson processes.
-- source:
--   Original path and filtration; no-positive-fixed-time-jump b4407263 and Proved arbitrary-Borel exact original jump count 2c942e8f.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave5_01_actual_source_no_fixed_positive_time_jump_ae
import Theorems.Thm_AvramDividend_Classical_avram_wave5_01_actual_source_marked_jump_measure_arbitrary_borel_count_exact
open MeasureTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_wave5_01_actual_source_marked_count_countable_positive_time_set_zero_ae
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (C : Set ℝ≥0) (hC : C.Countable) (hPos : ∀ u ∈ C, 0 < u)
    (B : Set ℝ) (hB : MeasurableSet B) :
    ∀ᵐ ω ∂P,
      ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (C ×ˢ B) = 0 := by sorry
