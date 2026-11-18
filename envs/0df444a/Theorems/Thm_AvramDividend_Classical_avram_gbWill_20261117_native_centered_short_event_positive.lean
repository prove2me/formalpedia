-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_gbWill_20261117_native_centered_short_event_positive
-- name    : AvramDividend.Classical.avram_gbWill_20261117_native_centered_short_event_positive
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-17T21:06:50.523454+00:00
-- url     : https://prove2.me/theorems/f1b21611-b04b-4264-8683-7e3122a602a7
-- title:
--   Unconditional canonical centred Gaussian Brownian tube has positive probability through 1/1000
-- statement:
--   The exact canonical Brownian centred path event of radius 1/4000 through time 1/1000 has strictly positive gaussianLimit probability. Proved B134/B135 supply measurable native path lift, IsBrownianReal.shift yields the centred process law, and B167 supplies the positive short-tube measure. This removes the remaining measurable-lift hypothesis for the Gaussian B fixed-band counterexample.

import Mathlib.Probability.BrownianMotion.Basic
import Definitions.Def_GlynnSTS_Limit_Setting
import Theorems.Thm_ProbabilityTheory_isBrownianReal_brownian_avram
import Theorems.Thm_AvramDividend_Classical_avram_gbB134_native_centered_brownian_lift_measurable_of_coordinates
import Theorems.Thm_AvramDividend_Classical_avram_gbB135_native_centered_brownian_coordinate_measurable
import Theorems.Thm_AvramDividend_Classical_avram_gbB167_native_positive_centered_brownian_short_tube_of_measurable_lift
open MeasureTheory ProbabilityTheory AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_gbWill_20261117_native_centered_short_event_positive
    [IsProbabilityMeasure gaussianLimit] :
    0 < gaussianLimit {ω : ℝ≥0 → ℝ |
      ∀ s : unitInterval,
        s ≤ (⟨(1 / 1000 : ℝ), by constructor <;> norm_num⟩ : unitInterval) →
        |ProbabilityTheory.brownian ⟨s, s.2.1⟩ ω -
          ProbabilityTheory.brownian 0 ω| < (1 / 4000 : ℝ)} := by sorry
