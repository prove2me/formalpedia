-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave6_04_actual_negative_generator_exact_ruin_landing_small_mark_truncation
-- name    : AvramDividend.Classical.avram_wave6_04_actual_negative_generator_exact_ruin_landing_small_mark_truncation
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-02T09:02:07.760418+00:00
-- url     : https://prove2.me/theorems/b34e7bc3-9312-4be2-850b-ae2784f91d32
-- title:
--   Actual source exact ruin landing includes derivative correction exactly for reserves below one
-- statement:
--   For the original spectrally negative Lévy generator integrand and exact negative jump z=-y landing at ruin zero, show that the small-mark subtraction uses the derivative if 0<y<1, whereas y≥1 has no derivative correction because the original truncation is the open interval (-1,1). Retain w(0), do not incorrectly replace it by zero or silently include the mark -1.
-- source:
--   Wave6 Chat04 exact source generator small-mark truncation at ruin landing; no generic compensator or martingale assumption.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_wave6_04_actual_negative_generator_exact_ruin_landing_small_mark_truncation
    (w : ℝ → ℝ) (y : ℝ) (hy : 0 < y) :
    SpectrallyNegativeLevy.generatorIntegrand w y (-y) =
      if y < 1 then w 0 - w y + y * deriv w y
      else w 0 - w y := by sorry
