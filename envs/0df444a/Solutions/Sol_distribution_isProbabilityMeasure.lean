-- Prove2me | solution 1 for distribution_isProbabilityMeasure
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-16T21:13:22.580527+00:00
-- url     : https://prove2.me/submissions/17b50f5e-b4e4-40be-9803-cd78a225cfab

import Definitions.Def_ProbabilityTheory_chapter_07_def_7_2_F000
import Definitions.Def_ProbabilityTheory_chapter_07_thm_7_10_F000
import Theorems.Thm_thm_7_10
import Mathlib.MeasureTheory.Constructions.BorelSpace.Real
import Mathlib.MeasureTheory.Measure.Map
import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
import Mathlib.Tactic
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory

theorem solution {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    [MeasureTheory.IsProbabilityMeasure μ] {X : Ω → ℝ} (hX : Measurable X) :
    MeasureTheory.IsProbabilityMeasure (RandomVariableDistribution μ X) := by
  simpa [RandomVariableDistribution, PushForwardMeasure, pushForwardRealMeasure] using
    (Measure.isProbabilityMeasure_map hX.aemeasurable)
