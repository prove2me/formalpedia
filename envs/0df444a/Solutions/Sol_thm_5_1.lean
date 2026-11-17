-- Prove2me | solution 1 for thm_5_1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-16T21:13:49.536111+00:00
-- url     : https://prove2.me/submissions/334fb7b2-cccc-4957-b478-9a17bf053b95

import Definitions.Def_ProbabilityTheory_chapter_05_def_5_2_F000
import Definitions.Def_ProbabilityTheory_chapter_05_def_5_3_F000
import Definitions.Def_ProbabilityTheory_chapter_05_def_5_4_F000
import Mathlib.MeasureTheory.Measure.MeasureSpaceDef
import Mathlib.Probability.Independence.Basic
import Mathlib.Tactic

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

theorem solution {Ω β γ : Type _} [MeasurableSpace Ω] [MeasurableSpace β] [MeasurableSpace γ]
    (μ : MeasureTheory.Measure Ω) [MeasureTheory.IsZeroOrProbabilityMeasure μ]
    (X : Ω → β) (Y : Ω → γ) :
    def_5_2 μ X Y ↔
      def_5_4 μ {s | @MeasurableSet Ω (def_5_3 X) s} {t | @MeasurableSet Ω (def_5_3 Y) t} := by
  simpa [def_5_2, def_5_3, def_5_4] using
    (ProbabilityTheory.IndepFun_iff_Indep X Y μ).trans
      (ProbabilityTheory.Indep_iff_IndepSets _ _ μ)
