-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave8_22_original_BV_value_measurable_of_positive_continuity
-- name    : AvramDividend.Classical.avram_wave8_22_original_BV_value_measurable_of_positive_continuity
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T09:10:53.657786+00:00
-- url     : https://prove2.me/theorems/4adbe17d-36d4-4a28-a23d-0a1698508c4b
-- title:
--   Original BV scale/value Borel measurability across its allowed origin jump
-- statement:
--   A genuine bounded-variation barrier value may be discontinuous at the origin. Its source assumptions give continuity for y≥0 and zero for y<0, which yield a globally Borel measurable value function by piecewise continuous measurability. This removes hWMeas from the original physical Lévy generator joint-measurability component hypotheses.
-- source:
--   Original Avram BV value-function regularity, pinned ContinuousOn.measurable_piecewise and measurableSet_Ici in Mathlib 0df444a.

import Mathlib
open MeasureTheory Set Filter Topology
open scoped NNReal ENNReal Classical
noncomputable section

theorem AvramDividend.Classical.avram_wave8_22_original_BV_value_measurable_of_positive_continuity (w : ℝ → ℝ)
  (hw_cont : ContinuousOn w (Ici (0 : ℝ)))
  (hw_neg : ∀ y : ℝ, y < 0 → w y = 0) :
  Measurable w := by sorry
