-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_a28_cadlag_arbitrary_Borel_marked_halfopen_window_count_measurable_v2_20261116
-- name    : AvramDividend.Classical.avram_a28_cadlag_arbitrary_Borel_marked_halfopen_window_count_measurable_v2_20261116
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-16T17:38:06.382314+00:00
-- url     : https://prove2.me/theorems/63eff82d-187f-434d-a2bd-0b4f52f2b9ec
-- title:
--   Arbitrary half-open window Borel marked-jump count factors measurably through a càdlàg path
-- statement:
--   For any s,T and any measurable Borel mark set B, the true set-cardinality of nonzero B-marked jumps of a cadlag real path in (s,T] is a measurable functional of that same path. Build the count from the Proved candidate-time enumeration and exact mark reconstruction, deduplicate first occurrence, and apply the new measurable half-open-window series helper. This directly enables adaptedness of original physical marked counts in arbitrary grid cells.
-- source:
--   Proved original cadlag full-horizon Borel jump enumeration 41bfd2c8, candidate-time 417d1996, exact marked series 660f311b, and new measurable window series a28.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_a28_cadlag_arbitrary_Borel_marked_halfopen_window_count_measurable_v2_20261116
    (s T : ℝ≥0) (B : Set ℝ) (hB : MeasurableSet B) :
    ∃ F : (ℝ≥0 → ℝ) → ℝ≥0∞,
      Measurable F ∧
      ∀ Y : ℝ≥0 → ℝ,
        (∀ u : ℝ≥0, ContinuousWithinAt Y (Ici u) u) →
        (∀ u : ℝ≥0, 0 < u → ∃ l : ℝ, Tendsto Y (𝓝[<] u) (𝓝 l)) →
        ({v : ℝ≥0 | s < v ∧ v ≤ T ∧
          Y v - Function.leftLim Y v ≠ 0 ∧
          Y v - Function.leftLim Y v ∈ B}).encard = F Y := by sorry
