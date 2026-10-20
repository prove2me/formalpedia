-- Prove2me | solution 1 for p2m_abs_le_normInf
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-19T16:18:04.887984+00:00
-- url     : https://prove2.me/submissions/fcf7e822-a5c5-439c-940e-63ec9acde569

import Mathlib.Data.Set.Finite.Range
import Definitions.Def_VanderbeiLP_PathFollowing_PathFollowingMethod
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true
open Matrix VanderbeiLP.PathFollowing
open scoped VanderbeiLP.PathFollowing
theorem solution {k : ℕ} (v : Fin k → ℝ) (i : Fin k) :
    |v i| ≤ normInf v := by
  unfold normInf
  exact le_csSup (Set.finite_range _).bddAbove (Set.mem_range_self i)
