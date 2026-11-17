-- Prove2me | solution 1 for simpleFunctionIntegralFinChain_zero
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-16T21:31:23.278841+00:00
-- url     : https://prove2.me/submissions/a5b72c93-d870-4b8e-a6ee-1683aa2dea55

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

theorem solution (μ : Measure Ω) (F : Fin 0 → SimpleFunc Ω EReal) :
    simpleFunctionIntegralFinChain μ 0 F = some 0 := by
  simp [simpleFunctionIntegralFinChain]
