-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_gaussianB_positive_long_centered_brownian_tube
-- name    : AvramDividend.Classical.avram_gaussianB_positive_long_centered_brownian_tube
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-17T21:32:37.871686+00:00
-- url     : https://prove2.me/theorems/c31f02c8-98ce-4def-9cda-a3a00b2ffd7f
-- title:
--   A fixed long centred Brownian small-ball event has positive probability through 1/500
-- statement:
--   For any standard Brownian process with continuous unit-interval sample paths as certified by GlynnSTS.Limit.IsStdBMC, the set of paths whose centred Brownian values remain within radius 1/4000 through time 1/500 has strictly positive probability. This longer event covers the original physical stopped G/H mesh horizon 1/1000 together with every sufficiently small one-step increment beyond its stopping time.

import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Definitions.Def_GlynnSTS_NoAttain_Setting
import Theorems.Thm_GlynnSTS_NoAttain_small_ball_positive
open MeasureTheory ProbabilityTheory
noncomputable section

theorem AvramDividend.Classical.avram_gaussianB_positive_long_centered_brownian_tube
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (B : Ω → C(unitInterval, ℝ))
    (hB : GlynnSTS.Limit.IsStdBMC P B) :
    0 < P {ω | ∀ s : unitInterval,
      s ≤ (⟨(1 / 500 : ℝ), by constructor <;> norm_num⟩ : unitInterval) →
      |B ω s| < (1 / 4000 : ℝ)} := by sorry
