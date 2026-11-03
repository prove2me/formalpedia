-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave6_04_actual_source_negative_mark_generator_exact_small_large_truncation_split
-- name    : AvramDividend.Classical.avram_wave6_04_actual_source_negative_mark_generator_exact_small_large_truncation_split
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-02T09:01:47.665654+00:00
-- url     : https://prove2.me/theorems/f6a26339-96ba-4dfb-9a17-4bd7fd44fe74
-- title:
--   Original source generator negative-mark split has exact small derivative compensation and full large jumps
-- statement:
--   For the genuine SpectrallyNegativeLevy.generatorIntegrand and all payoffs w and reserve levels y, prove the exact negative Lévy mark decomposition: on -1<z<0 subtract deriv w y*z; on z≤-1 do not subtract any derivative term. In particular the original truncation boundary z=-1 is fully uncompensated. This is the algebraic source-target split for C² Itô–Meyer and generator compensation.
-- source:
--   Wave6 Chat04 unfolded original generatorIntegrand and original Ioo(-1,1) source truncation.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_wave6_04_actual_source_negative_mark_generator_exact_small_large_truncation_split
    (w : ℝ → ℝ) (y : ℝ) :
    (∀ z : ℝ, -1 < z → z < 0 →
      SpectrallyNegativeLevy.generatorIntegrand w y z =
        w (y + z) - w y - deriv w y * z) ∧
    (∀ z : ℝ, z ≤ -1 →
      SpectrallyNegativeLevy.generatorIntegrand w y z =
        w (y + z) - w y) := by sorry
