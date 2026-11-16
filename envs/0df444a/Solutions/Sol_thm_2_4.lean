-- Prove2me | solution 1 for thm_2_4
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-15T09:23:06.604535+00:00
-- url     : https://prove2.me/submissions/188e0365-7fa6-413e-a5b7-4d0c942b9476

import Definitions.Def_ProbabilityTheory_chapter_02_def_2_6_F000
import Mathlib.MeasureTheory.Measure.MeasureSpace
import Mathlib.Tactic

open MeasureTheory Set
open scoped BigOperators


theorem solution {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) (A : ℕ → Set Ω)
    (hA : SetSeqIncreasing A) (hAmeas : ∀ n, MeasurableSet (A n)) :
    μ (⋃ i, A i) = ⨆ i, μ (A i) := by
  exact hA.measure_iUnion

