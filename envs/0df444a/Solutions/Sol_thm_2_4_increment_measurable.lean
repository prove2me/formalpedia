-- Prove2me | solution 1 for thm_2_4_increment_measurable
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-16T22:04:04.282177+00:00
-- url     : https://prove2.me/submissions/efe0d062-ee94-4d49-b1d0-7e1d848fd9c3

import Definitions.Def_ProbabilityTheory_chapter_02_thm_2_4_F000
import Definitions.Def_ProbabilityTheory_chapter_02_def_2_6_F000
import Mathlib.MeasureTheory.Measure.MeasureSpace
import Mathlib.Tactic
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped BigOperators

theorem solution {Ω : Type*} [MeasurableSpace Ω]
    {A : ℕ → Set Ω} (hAmeas : ∀ n, MeasurableSet (A n)) :
    ∀ n, MeasurableSet (thm_2_4_increment A n) := by
  intro n
  cases n with
  | zero =>
      simpa [thm_2_4_increment] using hAmeas 0
  | succ n =>
      simpa [thm_2_4_increment] using (hAmeas (n + 1)).diff (hAmeas n)
