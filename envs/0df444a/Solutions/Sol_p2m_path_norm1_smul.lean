-- Prove2me | solution 1 for p2m_path_norm1_smul
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-19T16:37:20.8787+00:00
-- url     : https://prove2.me/submissions/788eb69e-8df4-4f93-8a34-754675fdc480

import Mathlib.Algebra.BigOperators.Ring.Finset
import Definitions.Def_VanderbeiLP_PathFollowing_PathFollowingMethod
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true
open Matrix VanderbeiLP.PathFollowing
section
open scoped VanderbeiLP.PathFollowing in
theorem solution {k : ℕ} (a : ℝ) (ha : 0 ≤ a) (v : Fin k → ℝ) :
    norm1 (a • v) = a * norm1 v := by
  simp [norm1, Pi.smul_apply, smul_eq_mul, abs_mul, abs_of_nonneg ha,
    Finset.mul_sum]
end
