-- Prove2me | solution 1 for thm_2_5_gap_measurable
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-16T21:31:38.910912+00:00
-- url     : https://prove2.me/submissions/e1275e7c-80b8-40f8-abb0-897092b4528b

import Definitions.Def_ProbabilityTheory_chapter_02_thm_2_5_F000
import Definitions.Def_ProbabilityTheory_chapter_02_def_2_6_F000
import Mathlib.MeasureTheory.Measure.MeasureSpace
import Mathlib.Tactic
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set

theorem solution {Ω : Type*} [MeasurableSpace Ω]
    {A : ℕ → Set Ω} (hMeas : ∀ i, MeasurableSet (A i)) :
    ∀ i, MeasurableSet (thm_2_5_gap A i) := by
  intro i
  exact (hMeas 0).diff (hMeas i)
