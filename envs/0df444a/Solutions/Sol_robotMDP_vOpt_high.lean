-- Prove2me | solution 1 for robotMDP_vOpt_high
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T01:45:56.153018+00:00
-- url     : https://prove2.me/submissions/39ffb75b-f646-4b34-8076-542db6f247f1

import Definitions.Def_Mdp_PolicyIteration
import Definitions.Def_Mdp_RecyclingRobot
import Theorems.Thm_robotMDP_vOpt

set_option autoImplicit true
open Mdp Mdp.DiscountedMDP
theorem _root_.solution : robotMDP.vOpt RobotState.high = 10 / 3 := by
  rw [robotMDP_vOpt]; simp [robotV0]
