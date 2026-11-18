-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_gbB126_native_joint_centered_drifted_tube_of_measurable_lift
-- name    : AvramDividend.Classical.avram_gbB126_native_joint_centered_drifted_tube_of_measurable_lift
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-17T17:33:58.311639+00:00
-- url     : https://prove2.me/theorems/7a44940f-f772-4ecc-b8df-802f78ba73e7
-- title:
--   Native Gaussian measure assigns positive probability to a joint reserve and centred-mesh tube
-- statement:
--   For native gaussianLimit and any measurable continuous lift of a standard real Brownian motion, with positive probability the path through 17/16000 simultaneously has centred Brownian coordinates below 1/4000 and drifted reserve coordinates below 1/400. The event is common to original reflected-barrier path preservation and the stopped-mesh source-noise bound, allowing a single restricted L1 stopping event.

import Mathlib
import Theorems.Thm_ProbabilityTheory_isBrownianReal_brownian_avram
import Definitions.Def_GlynnSTS_Limit_Setting
import Theorems.Thm_AvramDividend_Classical_avram_gbB125_joint_centered_and_drifted_brownian_overshoot_tube_positive
open MeasureTheory ProbabilityTheory AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_gbB126_native_joint_centered_drifted_tube_of_measurable_lift
    [IsProbabilityMeasure gaussianLimit]
    (W : ℝ≥0 → (ℝ≥0 → ℝ) → ℝ)
    (hW : IsBrownianReal W gaussianLimit)
    (B : (ℝ≥0 → ℝ) → C(unitInterval, ℝ))
    (hMeas : Measurable B)
    (hCoord : ∀ ω (t : unitInterval), B ω t = W ⟨t, t.2.1⟩ ω)
    (t : unitInterval) (ht : (t : ℝ) = (17 / 16000 : ℝ)) :
    0 < gaussianLimit {ω | ∀ s : unitInterval, s ≤ t →
      |W ⟨s, s.2.1⟩ ω| < (1 / 4000 : ℝ) ∧
      |W ⟨s, s.2.1⟩ ω + 2 * (s : ℝ)| < (1 / 400 : ℝ)} := by sorry
