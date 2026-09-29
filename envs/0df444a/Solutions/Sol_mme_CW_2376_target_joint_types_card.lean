-- Prove2me | solution 1 for mme_CW_2376_target_joint_types_card
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-08-24T21:50:49.126559+00:00
-- url     : https://prove2.me/submissions/e8f77743-f884-474e-b616-5c2d2394d719

import Definitions.Def_mme_CW_2376_profile_dominance_weights

open MME

set_option autoImplicit false

/-- There are exactly fifteen supported joint grade triples in the squared
CW five-grading. -/
theorem solution :
    cw2376TargetJointTypes.card = 15 ∧
      Fintype.card {sigma : Fin 3 → Fin 5 //
        sigma ∈ cw2376TargetJointTypes} = 15 := by
  decide
