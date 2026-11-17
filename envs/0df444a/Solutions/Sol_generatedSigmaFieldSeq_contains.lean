-- Prove2me | solution 1 for generatedSigmaFieldSeq_contains
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-16T21:30:13.471761+00:00
-- url     : https://prove2.me/submissions/f5259d9d-6297-4dc7-a2d8-61bb3f23851a

import Definitions.Def_ProbabilityTheory_chapter_02_def_2_7_F000
import Theorems.Thm_generatedSigmaField_contains
import Mathlib.MeasureTheory.Measure.MeasureSpace
import Mathlib.Tactic
import Theorems.Thm_thm_2_6
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Set MeasureTheory

theorem solution {Ω : Type*} (B : ℕ → Set Ω) (n : ℕ) :
    @MeasurableSet Ω (generatedSigmaFieldSeq B) (B n) := by
  exact generatedSigmaField_contains (Set.range B) (B n) ⟨n, rfl⟩
