-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bv_zero13_original_first_negative_jump_inf_isStoppingTime
-- name    : AvramDividend.Classical.avram_bv_zero13_original_first_negative_jump_inf_isStoppingTime
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-09T11:04:09.995798+00:00
-- url     : https://prove2.me/theorems/48fcb9f3-78c0-4f8f-b5a7-fa55b15ac2b8
-- title:
--   Actual first physical strictly negative Levy jump is original right-continuous-filtration stopping time
-- statement:
--   For the original finite-negative-activity bounded-variation spectrally negative Levy process, the infimum of actual strictly negative physical jump times, with top when none, is a stopping time for the original right-continuous filtration. Choose deterministic countably dense observations in NNReal, apply the Proved original cutoff-count observed stopping result and pathwise observed-to-physical first-jump equality. No auxiliary compound Poisson source or new filtration.
-- source:
--   Original stopped zero-reserve intervals require the genuine first negative source jump as a stopping clock, to invoke Proved original future nojump drift laws and right-continuous stopped-history independence with exact dividend/ruin chronology.

import Mathlib.Probability.Process.Stopping
import Mathlib.MeasureTheory.Measure.Count
import Mathlib.Topology.Order.LeftRightLim
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_bv_zero13_original_countably_observed_negative_cutoff_first_clock_stopping
import Theorems.Thm_AvramDividend_Classical_avram_bv_zero13_original_dense_observed_first_clock_eq_actual_negative_jump_inf

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_bv_zero13_original_first_negative_jump_inf_isStoppingTime
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hBV : X.BoundedVariation)
    (hFinite : X.ν (Iio (0 : ℝ)) < ⊤) :
    IsStoppingTime 𝓕.rightCont
      (fun ω : Ω =>
        ⨅ u : ℝ≥0,
          if 0 < u ∧
              X.X u ω -
                Function.leftLim (fun v : ℝ≥0 => X.X v ω) u < 0
          then (u : WithTop ℝ≥0) else ⊤) := by sorry
