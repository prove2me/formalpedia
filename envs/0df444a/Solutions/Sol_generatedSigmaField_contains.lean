-- Prove2me | solution 1 for generatedSigmaField_contains
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-16T21:22:26.53486+00:00
-- url     : https://prove2.me/submissions/30e9aaea-d06f-4be4-9051-f41475bf0f0d

import Definitions.Def_ProbabilityTheory_chapter_02_def_2_7_F000
import Mathlib.MeasureTheory.Measure.MeasureSpace
import Mathlib.Tactic
import Theorems.Thm_thm_2_6
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Set MeasureTheory

theorem solution {Ω : Type*} (C : Set (Set Ω)) :
    ∀ s ∈ C, @MeasurableSet Ω (generatedSigmaField C) s :=
  (thm_2_6 C).1
