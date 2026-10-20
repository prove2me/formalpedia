-- Prove2me | solution 1 for p2m_norm1_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-19T16:16:50.976521+00:00
-- url     : https://prove2.me/submissions/4f80ef73-532d-4cb9-a5e8-f5545adbcb03

import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Definitions.Def_VanderbeiLP_PathFollowing_PathFollowingMethod
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Matrix VanderbeiLP.PathFollowing
theorem solution {k : ℕ} (v : Fin k → ℝ) : 0 ≤ norm1 v := by
  unfold norm1
  exact Finset.sum_nonneg (fun _ _ => abs_nonneg _)
