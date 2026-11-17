-- Prove2me | solution 1 for nullMeasurableSet_of_mem_completionCollection
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-16T21:13:01.278616+00:00
-- url     : https://prove2.me/submissions/ec85174d-16aa-4f56-b7e5-0440cd7a231e

import Definitions.Def_ProbabilityTheory_chapter_03_thm_3_6_F000
import Theorems.Thm_measure_eq_zero_of_isNullSet
import Definitions.Def_ProbabilityTheory_chapter_03_def_3_9_F000
import Mathlib.MeasureTheory.Measure.NullMeasurable
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory
open Set

theorem solution {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} {s : Set Ω} (hs : s ∈ completionCollection μ) :
    NullMeasurableSet s μ := by
  rcases hs with ⟨A, N, hA, hN, rfl⟩
  exact hA.nullMeasurableSet.union (NullMeasurableSet.of_null (measure_eq_zero_of_isNullSet hN))
