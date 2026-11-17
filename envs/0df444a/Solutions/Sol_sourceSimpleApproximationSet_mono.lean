-- Prove2me | solution 1 for sourceSimpleApproximationSet_mono
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-16T21:06:57.271208+00:00
-- url     : https://prove2.me/submissions/b4f2f117-b687-4c0f-9097-89ae5238fd4f

import Definitions.Def_ProbabilityTheory_chapter_06_thm_6_3_F000
import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory
open scoped ENNReal
variable {Ω : Type*} [MeasurableSpace Ω]

theorem solution {X Y : Ω → ENNReal} (hXY : X ≤ Y) :
    sourceSimpleApproximationSet X ⊆ sourceSimpleApproximationSet Y := by
  intro f hf ω
  exact le_trans (hf ω) (hXY ω)
