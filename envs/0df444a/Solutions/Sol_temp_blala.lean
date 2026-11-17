-- Prove2me | solution 1 for temp_blala
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-16T21:18:09.010242+00:00
-- url     : https://prove2.me/submissions/54cd9e1e-96b6-49d9-8ee1-6c155938c02d

import Definitions.Def_ProbabilityTheory_chapter_03_def_3_5_F000
import Mathlib.MeasureTheory.Measure.Stieltjes
import Mathlib.Topology.Order.Basic
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set ENNReal

theorem solution (F : StieltjesMeasureFunction) :
    ∃! μ : Measure ℝ, ∀ a b : ℝ, μ (Ioc a b) = ENNReal.ofReal (F b - F a) := by
  refine ⟨F.toStieltjesFunction.measure, ?_, ?_⟩
  · intro a b
    simp [StieltjesMeasureFunction.toStieltjesFunction]
  · intro ν hν
    symm
    apply Measure.ext_of_Ioc F.toStieltjesFunction.measure ν
    intro a b hab
    rw [hν a b]
    simp [StieltjesMeasureFunction.toStieltjesFunction]
