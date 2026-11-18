-- Prove2me | solution 1 for lowerSum_le_of_refinement
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-17T07:31:15.065619+00:00
-- url     : https://prove2.me/submissions/58be890d-0f86-4c62-9ac5-a184954bfa32

import Definitions.Def_ProbabilityTheory_chapter_01_def_1_2_F000
import Definitions.Def_ProbabilityTheory_chapter_01_thm_1_2_F009
import Mathlib.Tactic
import Theorems.Thm_DarbouxRS_partition_increment_nonneg_of_source_core
import Theorems.Thm_Refinement_subinterval_subset_of_mem_block
import Theorems.Thm_Refinement_sum_block_increment
import Theorems.Thm_Refinement_sum_blocks_eq_sum_univ
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Set DarbouxRS
open scoped BigOperators Pointwise
noncomputable section

theorem solution {a b : ℝ} {f α : ℝ → ℝ}
    (hs : SourceHypotheses a b f α)
    {P P' : Partition a b}
    (R : Refinement P P') :
    lowerSum P f α ≤ lowerSum P' f α := by
  classical
  rcases hs with ⟨hab, hfAbove, hfBelow, hαmono⟩

  unfold lowerSum

  calc
    (∑ i : Fin P.n,
      lowerStep P f i *
        (α (P.pts i.succ) - α (P.pts i.castSucc)))
        =
      ∑ i : Fin P.n,
        lowerStep P f i *
          (∑ j ∈  R.block i,
            (α (P'.pts j.succ) - α (P'.pts j.castSucc))) := by
        refine Finset.sum_congr rfl ?_
        intro i _hi
        rw [R.sum_block_increment i]

    _ =
      ∑ i : Fin P.n,
        ∑ j ∈  R.block i,
          lowerStep P f i *
            (α (P'.pts j.succ) - α (P'.pts j.castSucc)) := by
        refine Finset.sum_congr rfl ?_
        intro i _hi
        rw [Finset.mul_sum]

    _ ≤
      ∑ i : Fin P.n,
        ∑ j ∈  R.block i,
          lowerStep P' f j *
            (α (P'.pts j.succ) - α (P'.pts j.castSucc)) := by
        refine Finset.sum_le_sum ?_
        intro i _hi
        refine Finset.sum_le_sum ?_
        intro j hj

        have hsub :
            Partition.subinterval P' j ⊆ Partition.subinterval P i :=
          R.subinterval_subset_of_mem_block hj

        have hstep :
            lowerStep P f i ≤ lowerStep P' f j :=
          lowerStep_le_of_subinterval_subset P P' i j hfBelow hsub

        have hinc :
            0 ≤ α (P'.pts j.succ) - α (P'.pts j.castSucc) :=
          DarbouxRS.partition_increment_nonneg_of_source_core P'
            ⟨hab, hfAbove, hfBelow, hαmono⟩

        exact mul_le_mul_of_nonneg_right hstep hinc

    _ =
      ∑ j : Fin P'.n,
        lowerStep P' f j *
          (α (P'.pts j.succ) - α (P'.pts j.castSucc)) := by
        rw [R.sum_blocks_eq_sum_univ]

    _ = lowerSum P' f α := by
        rfl
namespace Partition

end Partition

-----------------------------------------------------------------------------
--  The Fundamental Darboux Inequality
-----------------------------------------------------------------------------
