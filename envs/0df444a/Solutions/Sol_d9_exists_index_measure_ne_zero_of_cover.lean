-- Prove2me | solution 1 for d9_exists_index_measure_ne_zero_of_cover
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-08T13:22:04.754903+00:00
-- url     : https://prove2.me/submissions/2ff8df6a-94cd-4325-ad8a-cdc908a9bfaa

import Mathlib
import Definitions.Def_NestedSeatAlloc_IntPolicy_Model
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory
open NestedSeatAlloc.IntPolicy
theorem solution
    {Ω ι : Type*} [MeasurableSpace Ω] [Countable ι]
    (μ : Measure Ω) (A : Set Ω) (E : ι → Set Ω)
    (hcover : A ⊆ ⋃ i, E i) (hA : μ A ≠ 0) :
    ∃ i, μ (E i) ≠ 0 := by
  by_contra h
  push_neg at h
  have hnull : μ (⋃ i, E i) = 0 :=
    (MeasureTheory.measure_iUnion_null_iff (μ := μ) (s := E)).2 h
  have hmono : μ A ≤ μ (⋃ i, E i) := MeasureTheory.measure_mono hcover
  have hA0 : μ A = 0 := by
    apply le_antisymm
    · simpa [hnull] using hmono
    · exact bot_le
  exact hA hA0
