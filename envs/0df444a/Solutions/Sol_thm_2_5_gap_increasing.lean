-- Prove2me | solution 1 for thm_2_5_gap_increasing
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-16T21:33:17.936203+00:00
-- url     : https://prove2.me/submissions/8dba5b05-4f5d-4e81-9579-d868bae0cca6

import Definitions.Def_ProbabilityTheory_chapter_02_thm_2_5_F000
import Definitions.Def_ProbabilityTheory_chapter_02_def_2_6_F000
import Mathlib.MeasureTheory.Measure.MeasureSpace
import Mathlib.Tactic
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set

theorem solution {Ω : Type*} {A : ℕ → Set Ω}
    (hA : SetSeqDecreasing A) :
    SetSeqIncreasing (thm_2_5_gap A) := by
  change Monotone (thm_2_5_gap A)
  intro i j hij x hx
  exact ⟨hx.1, fun hxAj => hx.2 (hA hij hxAj)⟩
