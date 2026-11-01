-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave4_04b_corrected_value_global_measurable
-- name    : AvramDividend.Classical.avram_wave4_04b_corrected_value_global_measurable
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-31T19:26:17.261991+00:00
-- url     : https://prove2.me/theorems/d03f0b93-60cb-4eb5-8df9-da3e199a74c3
-- title:
--   Corrected HJB boundary hypotheses imply global Borel measurability of the value function
-- statement:
--   Continuity of w on the nonnegative reserve half-line and zero extension on negative reserves, exactly as in the corrected unbounded-variation verification target, imply global Borel measurability even though twice continuous differentiability is assumed only in the strict capped interior. This enables predictable source Lévy jump-marked value increments crossing ruin.
-- source:
--   Use Mathlib ContinuousOn.measurable_piecewise on the closed nonnegative half-line and the zero function on its open negative complement; show the resulting piecewise function equals w everywhere.

import Mathlib

open MeasureTheory Set
open scoped Classical
noncomputable section

theorem AvramDividend.Classical.avram_wave4_04b_corrected_value_global_measurable
    (w : ℝ → ℝ)
    (hw_cont : ContinuousOn w (Ici 0))
    (hw_neg : ∀ y < 0, w y = 0) :
    Measurable w := by
  sorry
