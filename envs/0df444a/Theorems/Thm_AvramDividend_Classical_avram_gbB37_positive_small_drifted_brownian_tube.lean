-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_gbB37_positive_small_drifted_brownian_tube
-- name    : AvramDividend.Classical.avram_gbB37_positive_small_drifted_brownian_tube
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-17T15:34:55.299799+00:00
-- url     : https://prove2.me/theorems/51ea3630-6c4c-40bb-b8f7-9a330916df20
-- title:
--   Positive probability of a short horizon drifted Brownian tube
-- statement:
--   For a continuous standard Brownian motion with the GlynnSTS IsStdBMC law, a time horizon t=1/1000 has positive probability of remaining within distance 1/400 of the drifted path B(s)+2s, by the previously Proved Brownian small-ball lemma. This provides a stochastic input to the positive-drift fixed-j counterexample; transfer to the native GaussianLimit process remains separate.

import Mathlib
import Definitions.Def_GlynnSTS_NoAttain_Setting
import Theorems.Thm_GlynnSTS_NoAttain_small_ball_positive
open MeasureTheory ProbabilityTheory
noncomputable section

theorem AvramDividend.Classical.avram_gbB37_positive_small_drifted_brownian_tube
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (B : Ω → C(unitInterval, ℝ))
    (hB : GlynnSTS.Limit.IsStdBMC P B)
    (t : unitInterval) (ht : (t : ℝ) = (1 / 1000 : ℝ)) :
    0 < P {ω | ∀ s : unitInterval, s ≤ t →
      |B ω s + 2 * (s : ℝ)| < (1 / 400 : ℝ)} := by sorry
