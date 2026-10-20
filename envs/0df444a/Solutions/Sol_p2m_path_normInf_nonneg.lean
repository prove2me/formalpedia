-- Prove2me | solution 1 for p2m_path_normInf_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-19T16:37:51.869394+00:00
-- url     : https://prove2.me/submissions/d83eb60b-bb8e-4b16-8117-5fc35b4900e5

import Mathlib.Data.Set.Finite.Range
import Definitions.Def_VanderbeiLP_PathFollowing_PathFollowingMethod
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true
open Matrix VanderbeiLP.PathFollowing
section
open scoped VanderbeiLP.PathFollowing in
theorem solution {k : ℕ} (v : Fin k → ℝ) : 0 ≤ normInf v := by
  cases k with
  | zero => simp [normInf]
  | succ k =>
      unfold normInf
      exact le_trans (abs_nonneg (v 0))
        (le_csSup (Set.finite_range _).bddAbove (Set.mem_range_self 0))
end
