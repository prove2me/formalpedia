-- Prove2me | solution 1 for mme_stothers_phi233_fine_source_restrict_outer_block
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-09-02T23:18:50.52999+00:00
-- url     : https://prove2.me/submissions/9e91b939-cedb-4230-bd04-c84ad85be44f

import Mathlib.Tactic
import Definitions.Def_mme_stothers_phi233_profile_data
import Definitions.Def_mme_stothers_phi233_outer_grading
import Theorems.Thm_mme_stothers_phi233_fine_block_restrict_outer_block

open MME

universe u

set_option autoImplicit false
set_option warningAsError true

theorem solution
    {K : Type u} [Field K] (q : ℕ) (r : Fin 10) :
    TensorObj.Restrict
      (MME.StothersFourth.Phi233.fineSourceObj K q r)
      ((MME.StothersFourth.Phi233.outerGrading K q).blockSubtensor
        (MME.StothersFourth.Phi233.pattern r)) := by
  fin_cases r
  · exact
      mme_stothers_phi233_fine_block_restrict_outer_block (K := K) q
        (cwSquareBlockType 0 1 3) (cwSquareBlockType 2 2 0)
        (by intro s; fin_cases s <;> rfl)
  · exact
      mme_stothers_phi233_fine_block_restrict_outer_block (K := K) q
        (cwSquareBlockType 0 2 2) (cwSquareBlockType 2 1 1)
        (by intro s; fin_cases s <;> rfl)
  · exact
      mme_stothers_phi233_fine_block_restrict_outer_block (K := K) q
        (cwSquareBlockType 0 3 1) (cwSquareBlockType 2 0 2)
        (by intro s; fin_cases s <;> rfl)
  · exact
      mme_stothers_phi233_fine_block_restrict_outer_block (K := K) q
        (cwSquareBlockType 1 0 3) (cwSquareBlockType 1 3 0)
        (by intro s; fin_cases s <;> rfl)
  · exact
      mme_stothers_phi233_fine_block_restrict_outer_block (K := K) q
        (cwSquareBlockType 1 1 2) (cwSquareBlockType 1 2 1)
        (by intro s; fin_cases s <;> rfl)
  · exact
      mme_stothers_phi233_fine_block_restrict_outer_block (K := K) q
        (cwSquareBlockType 1 2 1) (cwSquareBlockType 1 1 2)
        (by intro s; fin_cases s <;> rfl)
  · exact
      mme_stothers_phi233_fine_block_restrict_outer_block (K := K) q
        (cwSquareBlockType 1 3 0) (cwSquareBlockType 1 0 3)
        (by intro s; fin_cases s <;> rfl)
  · exact
      mme_stothers_phi233_fine_block_restrict_outer_block (K := K) q
        (cwSquareBlockType 2 0 2) (cwSquareBlockType 0 3 1)
        (by intro s; fin_cases s <;> rfl)
  · exact
      mme_stothers_phi233_fine_block_restrict_outer_block (K := K) q
        (cwSquareBlockType 2 1 1) (cwSquareBlockType 0 2 2)
        (by intro s; fin_cases s <;> rfl)
  · exact
      mme_stothers_phi233_fine_block_restrict_outer_block (K := K) q
        (cwSquareBlockType 2 2 0) (cwSquareBlockType 0 1 3)
        (by intro s; fin_cases s <;> rfl)
