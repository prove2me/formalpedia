-- Prove2me | solution 1 for thm_2_4_countable_additivity_spine
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-16T23:27:25.753947+00:00
-- url     : https://prove2.me/submissions/78c5de7d-3f75-4e71-8fe8-28c87c4c1850

import Theorems.Thm_thm_2_4_increment_iUnion_eq
import Theorems.Thm_thm_2_4_tsum_eq_iSup_sum_range_succ
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

theorem solution {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (A : ℕ → Set Ω)
    (hA : SetSeqIncreasing A) (hAmeas : ∀ n, MeasurableSet (A n)) :
    μ (⋃ i, A i) = ∑' i, μ (thm_2_4_increment A i) := by
  rw [← thm_2_4_increment_iUnion_eq hA]
  exact measure_iUnion (thm_2_4_increment_pairwise_disjoint hA)
    (thm_2_4_increment_measurable hAmeas)
