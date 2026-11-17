-- Prove2me | solution 1 for thm_7_10
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-16T21:06:22.562896+00:00
-- url     : https://prove2.me/submissions/1c28fbe0-1cad-465a-8665-fc6dbeec528a

import Definitions.Def_ProbabilityTheory_chapter_07_thm_7_10_F000
import Mathlib.MeasureTheory.Constructions.BorelSpace.Real
import Mathlib.MeasureTheory.Measure.Map
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory

theorem solution {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) (X : Ω → ℝ)
    (hX : Measurable X) {B : Set ℝ} (hB : MeasurableSet B) :
    pushForwardRealMeasure μ X B = μ (X ⁻¹' B) := by
  simpa [pushForwardRealMeasure] using (Measure.map_apply hX hB)
