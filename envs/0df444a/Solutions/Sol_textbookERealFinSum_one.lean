-- Prove2me | solution 1 for textbookERealFinSum_one
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-16T23:31:25.520376+00:00
-- url     : https://prove2.me/submissions/1774f155-244c-4afe-98ef-bd17ff7587ec

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

theorem solution (f : Fin 1 → EReal) :
    textbookERealFinSum 1 f = some (f 0) := by
  change textbookERealAdd (f 0) 0 = some (f 0)
  simp [textbookERealAdd, textbookERealAddDefined]
