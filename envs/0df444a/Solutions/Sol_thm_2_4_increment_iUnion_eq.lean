-- Prove2me | solution 1 for thm_2_4_increment_iUnion_eq
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-16T23:26:03.169799+00:00
-- url     : https://prove2.me/submissions/d99714e0-f095-4431-9d47-dec260cf2f7b

import Definitions.Def_ProbabilityTheory_chapter_02_def_2_6_F000
import Definitions.Def_ProbabilityTheory_chapter_02_thm_2_4_F000
import Theorems.Thm_thm_2_4_increment_subset
import Theorems.Thm_thm_2_4_increment_pairwise_disjoint
import Theorems.Thm_thm_2_4_increment_measurable
import Mathlib.MeasureTheory.Measure.MeasureSpace
import Mathlib.Tactic
import Theorems.Thm_thm_2_4_partial_increment_union_eq
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped BigOperators

theorem solution {Ω : Type*} {A : ℕ → Set Ω}
    (hA : SetSeqIncreasing A) :
    (⋃ i, thm_2_4_increment A i) = ⋃ i, A i := by
  ext x
  constructor
  · intro hx
    rcases mem_iUnion.mp hx with ⟨i, hxi⟩
    exact mem_iUnion.mpr ⟨i, thm_2_4_increment_subset A i hxi⟩
  · intro hx
    rcases mem_iUnion.mp hx with ⟨n, hxAn⟩
    have hx_partial : x ∈ ⋃ i ∈ Set.Iic n, thm_2_4_increment A i := by
      rw [thm_2_4_partial_increment_union_eq hA n]
      exact hxAn
    rcases mem_iUnion.mp hx_partial with ⟨i, hi⟩
    rcases mem_iUnion.mp hi with ⟨_hi_le, hxB⟩
    exact mem_iUnion.mpr ⟨i, hxB⟩
