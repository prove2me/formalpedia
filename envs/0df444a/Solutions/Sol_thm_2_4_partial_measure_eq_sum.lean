-- Prove2me | solution 1 for thm_2_4_partial_measure_eq_sum
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-16T23:28:29.954162+00:00
-- url     : https://prove2.me/submissions/eec66db8-8f6c-4752-8458-9f8664e6fb59

import Theorems.Thm_thm_2_4_increment_iUnion_eq
import Theorems.Thm_thm_2_4_partial_increment_range_union_eq
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
    (hA : SetSeqIncreasing A) (hAmeas : ∀ n, MeasurableSet (A n)) (n : ℕ) :
    μ (A n) = ∑ i ∈ Finset.range (n + 1), μ (thm_2_4_increment A i) := by
  rw [← thm_2_4_partial_increment_range_union_eq hA n]
  exact measure_biUnion_finset
    (fun i _hi j _hj hij => thm_2_4_increment_pairwise_disjoint hA hij)
    (fun i _hi => thm_2_4_increment_measurable hAmeas i)
