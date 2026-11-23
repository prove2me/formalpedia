-- Prove2me | solution 1 for robotMDP_vOpt_low
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T01:46:05.743825+00:00
-- url     : https://prove2.me/submissions/5a1df610-293b-423c-a909-910a4c77083c

import Definitions.Def_Mdp_PolicyIteration
import Definitions.Def_Mdp_RecyclingRobot
import Theorems.Thm_robotMDP_vOpt

set_option autoImplicit true
open Mdp Mdp.DiscountedMDP
theorem _root_.solution : robotMDP.vOpt RobotState.low = 2 := by
  rw [robotMDP_vOpt]; simp [robotV0]
