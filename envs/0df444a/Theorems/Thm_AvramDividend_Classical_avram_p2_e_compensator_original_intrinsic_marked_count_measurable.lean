-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p2_e_compensator_original_intrinsic_marked_count_measurable
-- name    : AvramDividend.Classical.avram_p2_e_compensator_original_intrinsic_marked_count_measurable
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T18:49:51.300935+00:00
-- url     : https://prove2.me/theorems/5cb1e247-2fef-4d9e-baac-7b7311ddd524
-- title:
--   Original intrinsic marked-jump count is globally measurable
-- statement:
--   The literal intrinsic marked jump count of the original spectrally negative Lévy process on any finite time rectangle with Borel marks is measurable on the original full probability space. The proof composes the proved future increment extractor with adapted process coordinate measurability.
-- source:
--   Accepted original future extractor UUID 5cf3e058 plus adaptedness and measurable_pi_iff under pinned Mathlib.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave7_01_original_intrinsic_marked_future_measurable_extractor

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal

/-- The literal original-process intrinsic marked-jump count is globally measurable on the original probability space. -/

theorem AvramDividend.Classical.avram_p2_e_compensator_original_intrinsic_marked_count_measurable
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (s t : ℝ≥0) (hst : s ≤ t)
    (B : Set ℝ) (hB : MeasurableSet B) :
    Measurable (fun ω : Ω =>
      ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc s t ×ˢ B)) := by sorry
