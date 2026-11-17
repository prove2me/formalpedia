-- Prove2me | solution 1 for mem_completionCollection_iff_nullMeasurableSet
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-16T21:30:21.225479+00:00
-- url     : https://prove2.me/submissions/6ac7a457-5cc5-4079-bc68-d247d2e1b659

import Definitions.Def_ProbabilityTheory_chapter_03_thm_3_6_F000
import Theorems.Thm_measure_eq_zero_of_isNullSet
import Theorems.Thm_nullMeasurableSet_of_mem_completionCollection
import Theorems.Thm_mem_completionCollection_of_nullMeasurableSet
import Definitions.Def_ProbabilityTheory_chapter_03_def_3_9_F000
import Mathlib.MeasureTheory.Measure.NullMeasurable
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory
open Set

theorem solution {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (s : Set Ω) :
    s ∈ completionCollection μ ↔ NullMeasurableSet s μ := by
  constructor
  · exact nullMeasurableSet_of_mem_completionCollection
  · exact mem_completionCollection_of_nullMeasurableSet
