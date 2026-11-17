-- Prove2me | solution 1 for thm_2_4_increment_subset
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-16T21:13:57.279218+00:00
-- url     : https://prove2.me/submissions/ad1a27d9-9897-4676-802b-fcb17b158599

import Definitions.Def_ProbabilityTheory_chapter_02_thm_2_4_F000
import Definitions.Def_ProbabilityTheory_chapter_02_def_2_6_F000
import Mathlib.MeasureTheory.Measure.MeasureSpace
import Mathlib.Tactic
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped BigOperators

theorem solution {Ω : Type*} (A : ℕ → Set Ω) (n : ℕ) :
    thm_2_4_increment A n ⊆ A n := by
  cases n with
  | zero =>
      intro x hx
      simpa [thm_2_4_increment] using hx
  | succ n =>
      intro x hx
      exact hx.1
