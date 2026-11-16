-- Prove2me | solution 1 for thm_2_5
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-15T09:23:07.252693+00:00
-- url     : https://prove2.me/submissions/57c60868-04e5-4b5b-9992-9791f23de6e1

import Definitions.Def_ProbabilityTheory_chapter_02_thm_2_5_F000
import Definitions.Def_ProbabilityTheory_chapter_02_def_2_6_F000
import Mathlib.MeasureTheory.Measure.MeasureSpace
import Mathlib.Tactic
open MeasureTheory Set

theorem solution {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) (A : ℕ → Set Ω)
    (hA : SetSeqDecreasing A)
    (hMeas : ∀ i, MeasurableSet (A i))
    (hfin : μ (A 0) < ⊤) :
    μ (⋂ i, A i) = ⨅ i, μ (A i) := by
  exact Antitone.measure_iInter hA (fun i => (hMeas i).nullMeasurableSet) ⟨0, hfin.ne⟩

