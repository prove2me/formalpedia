-- Prove2me | solution 1 for p2m_path_norm1_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-19T16:37:29.91409+00:00
-- url     : https://prove2.me/submissions/9f726b90-1db5-4877-82a9-c3218403f012

import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Definitions.Def_VanderbeiLP_PathFollowing_PathFollowingMethod
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true
open Matrix VanderbeiLP.PathFollowing
section
open scoped VanderbeiLP.PathFollowing in
theorem solution {k : ℕ} (v : Fin k → ℝ) : 0 ≤ norm1 v := by
  unfold norm1
  exact Finset.sum_nonneg (fun _ _ => abs_nonneg _)
end
