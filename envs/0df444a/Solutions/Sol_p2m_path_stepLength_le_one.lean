-- Prove2me | solution 1 for p2m_path_stepLength_le_one
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-19T16:37:37.823715+00:00
-- url     : https://prove2.me/submissions/268be486-46a0-4f7e-806a-3919a4dae9c5

import Mathlib.Tactic.NormNum
import Definitions.Def_VanderbeiLP_PathFollowing_PathFollowingMethod
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true
open Matrix VanderbeiLP.PathFollowing
section
open scoped VanderbeiLP.PathFollowing in
theorem solution {m n : ℕ} (r : ℝ) (p d : PDPoint m n) :
    stepLength r p d ≤ 1 := by
  dsimp [stepLength]
  split_ifs
  · norm_num
  · exact min_le_right _ _
end
