-- Prove2me | solution 1 for independent_uncorrelated
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-16T21:21:19.650009+00:00
-- url     : https://prove2.me/submissions/3f9fd95f-1dc6-4202-8ce7-ac569bd92ef3

import Definitions.Def_ProbabilityTheory_chapter_07_def_7_3_F000
import Theorems.Thm_covariance_zero_iff_uncorrelated
import Definitions.Def_ProbabilityTheory_chapter_05_def_5_2_F000
import Definitions.Def_ProbabilityTheory_chapter_07_thm_7_13_F000
import Mathlib.MeasureTheory.Function.SimpleFunc
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Mathlib.Probability.Independence.Basic
import Mathlib.Probability.Independence.Integration
import Mathlib.Probability.Moments.Covariance
import Mathlib.Tactic
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory

theorem solution {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} {X Y : Ω → ℝ}
    (hXY : def_5_2 μ X Y) (hX : Integrable X μ) (hY : Integrable Y μ)
    (hXY_int : Integrable (fun ω => X ω * Y ω) μ) :
    Uncorrelated μ X Y := by
  exact thm_7_13 hXY hX hY hXY_int
