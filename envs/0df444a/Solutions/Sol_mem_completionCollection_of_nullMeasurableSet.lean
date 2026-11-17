-- Prove2me | solution 1 for mem_completionCollection_of_nullMeasurableSet
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-16T21:20:56.371802+00:00
-- url     : https://prove2.me/submissions/a3b1be61-2298-4500-95c0-cc35f85e1ab0

import Definitions.Def_ProbabilityTheory_chapter_03_thm_3_6_F000
import Theorems.Thm_measure_eq_zero_of_isNullSet
import Theorems.Thm_nullMeasurableSet_of_mem_completionCollection
import Definitions.Def_ProbabilityTheory_chapter_03_def_3_9_F000
import Mathlib.MeasureTheory.Measure.NullMeasurable
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory
open Set

theorem solution {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} {s : Set Ω} (hs : NullMeasurableSet s μ) :
    s ∈ completionCollection μ := by
  rcases NullMeasurableSet.exists_measurable_subset_ae_eq hs with ⟨A, hAsub, hAmeas, hAae⟩
  refine ⟨A, s \ A, hAmeas, ?_, (union_sdiff_cancel hAsub).symm⟩
  refine ⟨toMeasurable μ (s \ A), measurableSet_toMeasurable _ _, subset_toMeasurable _ _, ?_⟩
  have hdiff : μ (s \ A) = 0 := ae_le_set.1 hAae.symm.le
  simpa [measure_toMeasurable] using hdiff
