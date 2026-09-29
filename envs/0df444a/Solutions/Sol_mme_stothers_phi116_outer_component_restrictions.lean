-- Prove2me | solution 1 for mme_stothers_phi116_outer_component_restrictions
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-09-02T19:36:49.932822+00:00
-- url     : https://prove2.me/submissions/c7a23124-56f3-41af-a92b-b3d1be70e6a7

import Theorems.Thm_mme_stothers_phi116_fine_component_restrictions
import Theorems.Thm_mme_stothers_phi116_outer_fine_block_restrictions

open MME

universe u

set_option autoImplicit false

theorem solution
    {K : Type u} [Field K] :
    TensorObj.Restrict (MMObj K 12 1 12)
      ((MME.StothersFourth.Phi116.cwPhi116ThreeGrading K).blockSubtensor
        ![0, 1, 2]) ∧
    TensorObj.Restrict (MMObj K 12 1 12)
      ((MME.StothersFourth.Phi116.cwPhi116ThreeGrading K).blockSubtensor
        ![1, 0, 2]) ∧
    TensorObj.Restrict (coupledObj K 6)
      ((MME.StothersFourth.Phi116.cwPhi116ThreeGrading K).blockSubtensor
        ![0, 0, 0]) ∧
    TensorObj.Restrict (coupledObj K 6)
      ((MME.StothersFourth.Phi116.cwPhi116ThreeGrading K).blockSubtensor
        ![1, 1, 1]) := by
  obtain ⟨h012, h102, h000, h111⟩ :=
    mme_stothers_phi116_fine_component_restrictions (K := K)
  obtain ⟨b012, b102, b000, b111⟩ :=
    mme_stothers_phi116_outer_fine_block_restrictions K
  exact ⟨
    TensorObj.Restrict.trans h012 b012,
    TensorObj.Restrict.trans h102 b102,
    TensorObj.Restrict.trans h000 b000,
    TensorObj.Restrict.trans h111 b111⟩
