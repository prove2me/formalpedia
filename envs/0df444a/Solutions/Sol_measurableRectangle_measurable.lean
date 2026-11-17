-- Prove2me | solution 1 for measurableRectangle_measurable
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-16T21:07:13.519519+00:00
-- url     : https://prove2.me/submissions/dcd3a048-25ba-46a1-8f9a-fe904f523f76

import Definitions.Def_ProbabilityTheory_chapter_08_def_8_3_F000
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Mathlib.MeasureTheory.Measure.MeasureSpaceDef
import Mathlib.Tactic
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Set

theorem solution
    {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    {E₁ : Set α} {E₂ : Set β}
    (hE₁ : MeasurableSet E₁) (hE₂ : MeasurableSet E₂) :
    MeasurableSet (MeasurableRectangle E₁ E₂) := by
  exact hE₁.prod hE₂
