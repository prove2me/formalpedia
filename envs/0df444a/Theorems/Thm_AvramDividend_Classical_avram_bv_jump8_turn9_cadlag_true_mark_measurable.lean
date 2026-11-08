-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bv_jump8_turn9_cadlag_true_mark_measurable
-- name    : AvramDividend.Classical.avram_bv_jump8_turn9_cadlag_true_mark_measurable
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-07T08:31:49.07044+00:00
-- url     : https://prove2.me/theorems/24f7aabd-e775-43af-8e5f-4decf3d61530
-- title:
--   Actual càdlàg jump mark map and positive nonzero jump support are Borel
-- statement:
--   A càdlàg path has measurable left-limit marks. The positive nonzero jump-time set is measurable.
-- source:
--   A càdlàg path has measurable left-limit marks. The positive nonzero jump-time set is measurable.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section
attribute [local instance] Classical.propDecidable

theorem AvramDividend.Classical.avram_bv_jump8_turn9_cadlag_true_mark_measurable
    (Y : ℝ≥0 → ℝ)
    (hRight : ∀ u : ℝ≥0, ContinuousWithinAt Y (Ici u) u)
    (hLeft : ∀ u : ℝ≥0, 0 < u → ∃ l : ℝ,
      Tendsto Y (𝓝[<] u) (𝓝 l)) :
    Measurable (fun u : ℝ≥0 => (u, Y u - Function.leftLim Y u)) ∧
    MeasurableSet {u : ℝ≥0 | 0 < u ∧ Y u - Function.leftLim Y u ≠ 0} := by sorry
