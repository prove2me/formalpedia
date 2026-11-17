-- Prove2me | solution 1 for textbookERealFinSum_zero
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-16T21:31:30.522543+00:00
-- url     : https://prove2.me/submissions/e9e6427c-d6e4-4475-b7b4-87fe6be3127d

import Definitions.Def_ProbabilityTheory_chapter_06_def_6_2_F001
import Definitions.Def_ProbabilityTheory_chapter_06_def_6_2_F000
import Mathlib.MeasureTheory.Function.SimpleFunc
import Mathlib.Tactic
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory
open scoped BigOperators
variable {Ω : Type*} [MeasurableSpace Ω]

theorem solution (f : Fin 0 → EReal) :
    textbookERealFinSum 0 f = some 0 := by
  simp [textbookERealFinSum]
