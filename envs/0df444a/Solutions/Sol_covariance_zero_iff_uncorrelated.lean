-- Prove2me | solution 1 for covariance_zero_iff_uncorrelated
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-16T21:14:29.580148+00:00
-- url     : https://prove2.me/submissions/86f6d78b-cb24-4a7d-8c05-9a865c266f03

import Definitions.Def_ProbabilityTheory_chapter_07_def_7_3_F000
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

theorem solution {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsProbabilityMeasure μ] {X Y : Ω → ℝ} (hX : MemLp X 2 μ) (hY : MemLp Y 2 μ) :
    Covariance μ X Y = 0 ↔ Uncorrelated μ X Y := by
  rw [Covariance, ProbabilityTheory.covariance_eq_sub hX hY, Uncorrelated]
  rw [sub_eq_zero]
  simp [Pi.mul_apply]
