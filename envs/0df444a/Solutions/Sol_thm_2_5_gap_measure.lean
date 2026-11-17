-- Prove2me | solution 1 for thm_2_5_gap_measure
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-16T21:34:59.261765+00:00
-- url     : https://prove2.me/submissions/e9849eb9-fb5d-4932-afdc-f28435bb7661

import Definitions.Def_ProbabilityTheory_chapter_02_thm_2_5_F000
import Definitions.Def_ProbabilityTheory_chapter_02_def_2_6_F000
import Mathlib.MeasureTheory.Measure.MeasureSpace
import Mathlib.Tactic
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set

theorem solution {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    {A : ℕ → Set Ω} (hA : SetSeqDecreasing A)
    (hMeas : ∀ i, MeasurableSet (A i)) (hfin : μ (A 0) < ⊤) (i : ℕ) :
    μ (thm_2_5_gap A i) = μ (A 0) - μ (A i) := by
  have hAi_subset : A i ⊆ A 0 := hA (Nat.zero_le i)
  have hAi_fin : μ (A i) ≠ ⊤ :=
    ne_top_of_le_ne_top (ne_top_of_lt hfin) (measure_mono hAi_subset)
  exact measure_sdiff hAi_subset (hMeas i).nullMeasurableSet hAi_fin
