-- Prove2me | solution 1 for mme_stothers_phi134_fine_component_restrictions
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-09-02T20:45:58.54838+00:00
-- url     : https://prove2.me/submissions/6cdb447a-4465-43ec-a118-ffe31165f438

import Definitions.Def_mme_stothers_phi116_fine_blocks
import Definitions.Def_mme_tensor_bridge
import Theorems.Thm_mme_CW_fourth_fine_block_restrict_of_factors
import Theorems.Thm_mme_CW_square_canonical_elementary_blocks
import Theorems.Thm_mme_CW_square_canonical_coupled112_restrict
import Theorems.Thm_mme_CW_square_canonical_coupled121_restrict

open MME

universe u

set_option autoImplicit false

theorem solution
    {K : Type u} [Field K] (q : ℕ) :
    TensorObj.Restrict (MMObj K 1 (2 * q) 1)
      (MME.StothersFourth.Phi116.cwFourthFineBlockObj
        K q 0 0 4 1 3 0) ∧
    TensorObj.Restrict
      (TensorObj.kron (MMObj K 1 1 (2 * q))
        (TensorObj.permObj (cyclicPerm.trans cyclicPerm) (coupledObj K q)))
      (MME.StothersFourth.Phi116.cwFourthFineBlockObj
        K q 0 1 3 1 2 1) ∧
    TensorObj.Restrict
      (TensorObj.kron (MMObj K 1 1 (q ^ 2 + 2)) (coupledObj K q))
      (MME.StothersFourth.Phi116.cwFourthFineBlockObj
        K q 0 2 2 1 1 2) ∧
    TensorObj.Restrict (MMObj K (2 * q) 1 (2 * q))
      (MME.StothersFourth.Phi116.cwFourthFineBlockObj
        K q 0 3 1 1 0 3) ∧
    TensorObj.Restrict (MMObj K (2 * q) 1 (2 * q))
      (MME.StothersFourth.Phi116.cwFourthFineBlockObj
        K q 1 0 3 0 3 1) ∧
    TensorObj.Restrict
      (TensorObj.kron (coupledObj K q) (MMObj K 1 1 (q ^ 2 + 2)))
      (MME.StothersFourth.Phi116.cwFourthFineBlockObj
        K q 1 1 2 0 2 2) ∧
    TensorObj.Restrict
      (TensorObj.kron
        (TensorObj.permObj (cyclicPerm.trans cyclicPerm) (coupledObj K q))
        (MMObj K 1 1 (2 * q)))
      (MME.StothersFourth.Phi116.cwFourthFineBlockObj
        K q 1 2 1 0 1 3) ∧
    TensorObj.Restrict (MMObj K 1 (2 * q) 1)
      (MME.StothersFourth.Phi116.cwFourthFineBlockObj
        K q 1 3 0 0 0 4) := by
  obtain ⟨_, h004, _, _, h013, h031, h103, _, h130, _, h022, _, _⟩ :=
    mme_CW_square_canonical_elementary_blocks (K := K) q
  have h112 := mme_CW_square_canonical_coupled112_restrict (K := K) q
  have h121 := mme_CW_square_canonical_coupled121_restrict (K := K) q
  constructor
  · have hp := mme_CW_fourth_fine_block_restrict_of_factors
      q 0 0 4 1 3 0 h004 h130
    exact TensorObj.Restrict.trans
      (by simpa using (MMObj_kron_iso (K := K) 1 1 1 1 (2 * q) 1).2) hp
  constructor
  · exact mme_CW_fourth_fine_block_restrict_of_factors
      q 0 1 3 1 2 1 h013 h121
  constructor
  · exact mme_CW_fourth_fine_block_restrict_of_factors
      q 0 2 2 1 1 2 h022 h112
  constructor
  · have hp := mme_CW_fourth_fine_block_restrict_of_factors
      q 0 3 1 1 0 3 h031 h103
    exact TensorObj.Restrict.trans
      (by simpa using
        (MMObj_kron_iso (K := K) 1 1 (2 * q) (2 * q) 1 1).2) hp
  constructor
  · have hp := mme_CW_fourth_fine_block_restrict_of_factors
      q 1 0 3 0 3 1 h103 h031
    exact TensorObj.Restrict.trans
      (by simpa using
        (MMObj_kron_iso (K := K) (2 * q) 1 1 1 1 (2 * q)).2) hp
  constructor
  · exact mme_CW_fourth_fine_block_restrict_of_factors
      q 1 1 2 0 2 2 h112 h022
  constructor
  · exact mme_CW_fourth_fine_block_restrict_of_factors
      q 1 2 1 0 1 3 h121 h013
  · have hp := mme_CW_fourth_fine_block_restrict_of_factors
      q 1 3 0 0 0 4 h130 h004
    exact TensorObj.Restrict.trans
      (by simpa using (MMObj_kron_iso (K := K) 1 (2 * q) 1 1 1 1).2) hp
