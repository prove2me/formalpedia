-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave6_04_actual_source_zero_mark_generator_taylor_compensation_vanishes
-- name    : AvramDividend.Classical.avram_wave6_04_actual_source_zero_mark_generator_taylor_compensation_vanishes
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-02T09:18:32.25723+00:00
-- url     : https://prove2.me/theorems/5083045e-0ec7-41e9-9033-68fc8fbef942
-- title:
--   Original nonlinear source generator Taylor jump term vanishes at zero Lévy mark
-- statement:
--   The literal original SpectrallyNegativeLevy.generatorIntegrand is identically zero when its jump-mark argument is zero, for every payoff and reserve level. This formally justifies the nonzero-jump restriction in the intrinsic X.X jump-count NX while keeping the generator drift unchanged; no source intensity or martingale assumption is used.
-- source:
--   Wave6 Chat04 exact original generatorIntegrand truncation at zero Lévy mark; intrinsic jump-count consistency.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_wave6_04_actual_source_zero_mark_generator_taylor_compensation_vanishes
    (w : ℝ → ℝ) (y : ℝ) :
    SpectrallyNegativeLevy.generatorIntegrand w y 0 = 0 := by sorry
