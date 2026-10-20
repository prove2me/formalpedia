-- Prove2me | solution 1 for p2m_normInf_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-19T16:34:33.180398+00:00
-- url     : https://prove2.me/submissions/57d34994-1f15-4717-94c6-16e50fbab6e0

import Mathlib
import Definitions.Def_VanderbeiLP_PathFollowing_PathFollowingMethod
import Theorems.Thm_p2m_abs_le_normInf
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true
open Matrix VanderbeiLP.PathFollowing
open scoped VanderbeiLP.PathFollowing
theorem solution {k : ℕ} (v : Fin k → ℝ) : 0 ≤ normInf v := by
  cases k with
  | zero => simp [normInf]
  | succ k => exact le_trans (abs_nonneg (v 0)) (p2m_abs_le_normInf v 0)
