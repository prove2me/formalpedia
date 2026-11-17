-- Prove2me | solution 1 for thm_3_6
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-16T21:59:59.785598+00:00
-- url     : https://prove2.me/submissions/c47a2c4c-03b2-467d-b52f-83d7ec965d2e

import Theorems.Thm_mem_completionCollection_iff_nullMeasurableSet
import Theorems.Thm_completion_apply_union_isNullSet
import Definitions.Def_ProbabilityTheory_chapter_03_thm_3_6_F000
import Definitions.Def_ProbabilityTheory_chapter_03_def_3_9_F000
import Mathlib.MeasureTheory.Measure.NullMeasurable
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory
open Set

theorem solution {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) :
    (∀ s, s ∈ completionCollection μ ↔ NullMeasurableSet s μ) ∧
      (∀ A N, @MeasurableSet Ω ‹MeasurableSpace Ω› A →
        IsNullSet μ N → completionMeasure μ (A ∪ N) = μ A) ∧
      Measure.IsComplete (completionMeasure μ) := by
  refine
    ⟨fun s => mem_completionCollection_iff_nullMeasurableSet μ s,
      ?_,
      Measure.completion.isComplete μ⟩
  intro A N hA hN
  exact completion_apply_union_isNullSet μ hA hN
