-- Prove2me | solution 1 for mme_CW_2376_target_joint_types_iff_sum_four
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-08-24T22:40:34.189219+00:00
-- url     : https://prove2.me/submissions/751eedb4-6a29-473e-a59a-27d9a50dea63

import Definitions.Def_mme_CW_2376_joint_profile_table

open MME

set_option autoImplicit false
set_option maxRecDepth 10000

theorem solution
    (sigma : Fin 3 → Fin 5) :
    sigma ∈ cw2376TargetJointTypes ↔
      (sigma 0).val + (sigma 1).val + (sigma 2).val = 4 := by
  revert sigma
  decide
