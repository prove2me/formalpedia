-- Prove2me | solution 1 for exists_common_refinement
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-17T07:32:41.600954+00:00
-- url     : https://prove2.me/submissions/c0a910d8-4d64-4045-85ff-7b953867c693

import Definitions.Def_ProbabilityTheory_chapter_01_def_1_2_F000
import Definitions.Def_ProbabilityTheory_chapter_01_thm_1_2_F009
import Definitions.Def_ProbabilityTheory_chapter_01_thm_1_2_F013
import Mathlib.Tactic
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open scoped BigOperators Pointwise
open Set
noncomputable section

theorem solution {a b : ℝ} (P1 P2 : Partition a b) :
    ∃ P : Partition a b,
      ∃ _R1 : Refinement P1 P,
        ∃ _R2 : Refinement P2 P,
          True := by
  classical

  have hab : a < b := partition_endpoint_lt P1

  let s : Finset ℝ := P1.carrier ∪ P2.carrier

  have ha : a ∈ s := by
    exact Finset.mem_union_left _ P1.start_mem_carrier

  have hb : b ∈ s := by
    exact Finset.mem_union_left _ P1.end_mem_carrier

  have hsub : ↑s ⊆ Set.Icc a b := by
    intro x hx
    rcases Finset.mem_union.mp hx with hx1 | hx2
    · exact P1.carrier_subset_Icc hx1
    · exact P2.carrier_subset_Icc hx2

  let P : Partition a b :=
    Partition.ofFinset hab s ha hb hsub

  have hP1_exists :
      ∀ i : Fin (P1.n + 1),
        ∃ j : Fin (P.n + 1), P1.pts i = P.pts j := by
    intro i
    have hx : P1.pts i ∈ s := by
      exact Finset.mem_union_left _ (P1.pts_mem_carrier i)

    rcases Partition.ofFinset_contains hab s ha hb hsub hx with ⟨j, hj⟩
    exact ⟨j, hj.symm⟩

  have hP2_exists :
      ∀ i : Fin (P2.n + 1),
        ∃ j : Fin (P.n + 1), P2.pts i = P.pts j := by
    intro i
    have hx : P2.pts i ∈ s := by
      exact Finset.mem_union_right _ (P2.pts_mem_carrier i)

    rcases Partition.ofFinset_contains hab s ha hb hsub hx with ⟨j, hj⟩
    exact ⟨j, hj.symm⟩

  let R1 : Refinement P1 P :=
    Refinement.of_exists hP1_exists

  let R2 : Refinement P2 P :=
    Refinement.of_exists hP2_exists

  exact ⟨P, R1, R2, trivial⟩
-----------------------------------------------------------------------------
--  The Fundamental Darboux Inequality
-----------------------------------------------------------------------------
