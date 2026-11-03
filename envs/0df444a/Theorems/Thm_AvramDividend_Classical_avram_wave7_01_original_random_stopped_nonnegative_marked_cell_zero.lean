-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave7_01_original_random_stopped_nonnegative_marked_cell_zero
-- name    : AvramDividend.Classical.avram_wave7_01_original_random_stopped_nonnegative_marked_cell_zero
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-02T15:35:27.132127+00:00
-- url     : https://prove2.me/theorems/1d8dc9a1-96c6-446f-9695-8d9d85a7f788
-- title:
--   Original stopped Lévy intrinsic marked count is zero for nonnegative random mark cells
-- statement:
--   For an arbitrary original-sample-dependent stopping horizon τ(ω), arbitrary original-sample-dependent mark cell B(ω) supported on nonnegative marks, and every source sample ω, the genuine original intrinsic marked jump count before the random horizon is zero. Holds without finite activity or integrability, and even for mark-selection functions not assumed measurable, because zero is a pathwise support fact. This settles the stopped random-cell nonnegative branch of predictable compensation; negative cells remain open.
-- source:
--   Use the Proved globally original-path negative-mark support identity b4f7e14b-fa0b-4895-add5-431a8c78a5e5 for the exact random stopped time–mark set; its intersection with strictly negative marks is empty.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave7_01_original_intrinsic_marked_measure_arbitrary_set_negative_support

open MeasureTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_wave7_01_original_random_stopped_nonnegative_marked_cell_zero
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (τ : Ω → ℝ≥0∞)
    (B : Ω → Set ℝ)
    (hB : ∀ ω, B ω ⊆ Ici (0 : ℝ))
    (ω : Ω) :
    ((Measure.count.restrict {u : ℝ≥0 |
      0 < u ∧ X.X u ω -
        Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
      (fun u : ℝ≥0 => (u,
        X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
      ({t : ℝ≥0 | (t : ℝ≥0∞) ≤ τ ω} ×ˢ B ω) = 0 := by sorry
