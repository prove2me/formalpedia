-- Prove2me | solution 1 for thm_5_7
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-16T21:06:41.150878+00:00
-- url     : https://prove2.me/submissions/98aa9b4a-9213-4047-89ba-3ee0f902b84e

import Definitions.Def_ProbabilityTheory_chapter_05_def_5_5to10_F000
import Mathlib.MeasureTheory.Measure.MeasureSpaceDef
import Mathlib.Probability.Independence.Basic
import Mathlib.Tactic

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

theorem solution {Ω : Type _} [MeasurableSpace Ω] (μ : MeasureTheory.Measure Ω) {n : ℕ}
    (A : Fin n → Set Ω) :
    def_5_5 μ A ↔ ProbabilityTheory.iIndep (fun k : Fin n => MeasurableSpace.generateFrom {A k}) μ := by
  simpa [def_5_5] using (ProbabilityTheory.iIndepSet_iff_iIndep (s := A) (μ := μ))
