-- Prove2me | solution 1 for thm_2_5_gap_iUnion_eq
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-16T21:31:14.56986+00:00
-- url     : https://prove2.me/submissions/8dfaf6bd-e69f-4f6a-af86-8be54b84d9aa

import Definitions.Def_ProbabilityTheory_chapter_02_thm_2_5_F000
import Definitions.Def_ProbabilityTheory_chapter_02_def_2_6_F000
import Mathlib.MeasureTheory.Measure.MeasureSpace
import Mathlib.Tactic
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set

theorem solution {Ω : Type*} (A : ℕ → Set Ω) :
    (⋃ i, thm_2_5_gap A i) = A 0 \ ⋂ i, A i := by
  ext x
  simp [thm_2_5_gap]
