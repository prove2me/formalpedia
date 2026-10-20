-- Prove2me | solution 1 for p2m_norm1_smul
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-19T16:16:19.387848+00:00
-- url     : https://prove2.me/submissions/cde20a59-d7f7-4321-86db-3882d43830d3

import Mathlib.Algebra.BigOperators.Ring.Finset
import Definitions.Def_VanderbeiLP_PathFollowing_PathFollowingMethod
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Matrix VanderbeiLP.PathFollowing
theorem solution {k : ℕ} (a : ℝ) (ha : 0 ≤ a) (v : Fin k → ℝ) :
    norm1 (a • v) = a * norm1 v := by
  simp [norm1, Pi.smul_apply, smul_eq_mul, abs_mul, abs_of_nonneg ha,
    Finset.mul_sum]
