-- Prove2me | solution 1 for p2m_stepLength_le_one
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-19T16:17:35.067017+00:00
-- url     : https://prove2.me/submissions/15b52df2-43fe-4178-8f88-b9807c70692d

import Mathlib.Tactic.NormNum
import Definitions.Def_VanderbeiLP_PathFollowing_PathFollowingMethod
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true
open Matrix VanderbeiLP.PathFollowing
open scoped VanderbeiLP.PathFollowing
theorem solution {m n : ℕ} (r : ℝ) (p d : PDPoint m n) :
    stepLength r p d ≤ 1 := by
  dsimp [stepLength]
  split_ifs
  · norm_num
  · exact min_le_right _ _
