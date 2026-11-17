-- Prove2me | solution 1 for thm_2_4_partial_increment_range_union_eq
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-16T23:26:43.143568+00:00
-- url     : https://prove2.me/submissions/d4cdcc0e-efbf-4a9d-ba10-f3e157044d9b

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
    (hA : SetSeqIncreasing A) (n : ℕ) :
    (⋃ i ∈ Finset.range (n + 1), thm_2_4_increment A i) = A n := by
  rw [← thm_2_4_partial_increment_union_eq hA n]
  ext x
  simp [Finset.mem_range]
