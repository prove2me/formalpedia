-- Prove2me | solution 1 for textbookERealFinSum_succ
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-16T21:33:10.386215+00:00
-- url     : https://prove2.me/submissions/ba502b71-ecd8-41b7-9ec1-d6fd2a7c71be

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

theorem solution (n : ℕ) (f : Fin (n + 1) → EReal) :
    textbookERealFinSum (n + 1) f =
      textbookIntegralAdd (some (f 0)) (textbookERealFinSum n fun i => f i.succ) := by
  simp [textbookERealFinSum]
