-- Prove2me | solution 1 for thm_2_5_tendsto
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-15T09:23:07.882611+00:00
-- url     : https://prove2.me/submissions/63940a66-64ad-4bc3-9d18-44fd808d204e

import Definitions.Def_ProbabilityTheory_chapter_02_thm_2_5_F000
import Definitions.Def_ProbabilityTheory_chapter_02_def_2_6_F000
import Mathlib.MeasureTheory.Measure.MeasureSpace
import Mathlib.Tactic
open MeasureTheory Set

theorem solution {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (A : ℕ → Set Ω) (hA : SetSeqDecreasing A)
    (hMeas : ∀ i, MeasurableSet (A i)) (hfin : μ (A 0) < ⊤) :
    Filter.Tendsto (fun i => μ (A i)) Filter.atTop (nhds (μ (⋂ i, A i))) := by
  exact tendsto_measure_iInter_atTop (fun i => (hMeas i).nullMeasurableSet) hA ⟨0, hfin.ne⟩

