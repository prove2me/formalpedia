-- Prove2me | solution 1 for thm_2_4_tsum_eq_iSup_sum_range_succ
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-16T21:36:55.485488+00:00
-- url     : https://prove2.me/submissions/365617c5-0720-4be5-a31f-e3515f439e02

import Definitions.Def_ProbabilityTheory_chapter_02_def_2_6_F000
import Definitions.Def_ProbabilityTheory_chapter_02_thm_2_4_F000
import Mathlib.MeasureTheory.Measure.MeasureSpace
import Mathlib.Tactic
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped BigOperators

theorem solution (f : ℕ → ENNReal) :
    ∑' i, f i = ⨆ n, ∑ i ∈ Finset.range (n + 1), f i := by
  rw [ENNReal.tsum_eq_iSup_nat]
  apply le_antisymm
  · refine iSup_le fun n => ?_
    exact le_iSup_of_le n
      (Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono (Nat.le_succ n))
        (fun _i _hi _hnot => bot_le))
  · refine iSup_le fun n => ?_
    exact le_iSup_of_le (n + 1) le_rfl
