-- Prove2me | solution 1 for measure_eq_zero_of_isNullSet
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-16T21:06:50.003598+00:00
-- url     : https://prove2.me/submissions/fc97173d-f172-423e-9e1f-1993331f459d

import Definitions.Def_ProbabilityTheory_chapter_03_thm_3_6_F000
import Definitions.Def_ProbabilityTheory_chapter_03_def_3_9_F000
import Mathlib.MeasureTheory.Measure.NullMeasurable
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory
open Set

theorem solution {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} {N : Set Ω}
    (hN : IsNullSet μ N) : μ N = 0 := by
  rcases hN with ⟨E, hE, hNE, hE0⟩
  exact measure_mono_null hNE hE0
