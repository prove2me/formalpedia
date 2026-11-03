-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave6_04_actual_source_generator_negative_unit_mark_is_uncompensated
-- name    : AvramDividend.Classical.avram_wave6_04_actual_source_generator_negative_unit_mark_is_uncompensated
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-02T09:02:11.427882+00:00
-- url     : https://prove2.me/theorems/3a1e9991-272c-47ea-a65e-a509f5c142af
-- title:
--   Original source negative unit Lévy mark contributes the full jump without derivative compensation
-- statement:
--   At the exact negative mark z=-1, the genuine SpectrallyNegativeLevy.generatorIntegrand is w(y-1)-w(y), since the source compensates only the open interval (-1,1), not its left endpoint. This is the exact large-negative-mark boundary needed in the stopped nonlinear Itô–Meyer generator.
-- source:
--   Wave6 Chat04 exact original source Lévy truncation endpoint; independent of Chat01 intensity and Chat02 martingale isometry.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_wave6_04_actual_source_generator_negative_unit_mark_is_uncompensated
    (w : ℝ → ℝ) (y : ℝ) :
    SpectrallyNegativeLevy.generatorIntegrand w y (-1) =
      w (y - 1) - w y := by sorry
