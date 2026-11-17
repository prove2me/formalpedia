-- Prove2me | solution 1 for thm_5_2
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-16T21:13:31.679869+00:00
-- url     : https://prove2.me/submissions/2ef9d697-9816-4973-a578-5d94626bfd59

import Definitions.Def_ProbabilityTheory_chapter_05_def_5_2_F000
import Mathlib.Probability.Independence.Basic
import Mathlib.Tactic

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

theorem solution {Ω β γ β' γ' : Type _}
    [MeasurableSpace Ω] [MeasurableSpace β] [MeasurableSpace γ]
    [MeasurableSpace β'] [MeasurableSpace γ']
    (μ : MeasureTheory.Measure Ω) (X : Ω → β) (Y : Ω → γ)
    (f : β → β') (g : γ → γ')
    (hXY : def_5_2 μ X Y) (hf : Measurable f) (hg : Measurable g) :
    def_5_2 μ (f ∘ X) (g ∘ Y) := by
  have hxy : ProbabilityTheory.IndepFun X Y μ := by
    simpa [def_5_2] using hXY
  simpa [def_5_2, Function.comp] using (ProbabilityTheory.IndepFun.comp (hfg := hxy) hf hg)
