-- Prove2me | solution 1 for def62_eq_some_iff
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-16T21:27:05.015295+00:00
-- url     : https://prove2.me/submissions/19c7143b-9c8a-44cd-ae72-9fe206de54ec

import Definitions.Def_ProbabilityTheory_chapter_06_def_6_2_F001
import Definitions.Def_ProbabilityTheory_chapter_06_def_6_2_F000
import Mathlib.MeasureTheory.Function.SimpleFunc
import Mathlib.Tactic
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory
open scoped BigOperators
variable {Ω : Type*} [MeasurableSpace Ω]

theorem solution (μ : Measure Ω) (f : SimpleFunc Ω EReal) (v : EReal) :
    def_6_2 μ f = some v ↔
      simpleFunctionIntegralDefined μ f ∧ simpleFunctionIntegralValue μ f = v := by
  classical
  unfold def_6_2
  by_cases h : simpleFunctionIntegralDefined μ f
  · simp [h]
  · simp [h]

