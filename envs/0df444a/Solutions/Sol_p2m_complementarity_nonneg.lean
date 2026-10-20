-- Prove2me | solution 1 for p2m_complementarity_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-19T16:18:27.281114+00:00
-- url     : https://prove2.me/submissions/dcab2634-4167-4cb5-ad6e-cabc0f9b620a

import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Definitions.Def_VanderbeiLP_PathFollowing_PathFollowingMethod
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true
open Matrix VanderbeiLP.PathFollowing
open scoped VanderbeiLP.PathFollowing
theorem solution {m n : ℕ} (p : PDPoint m n)
    (hp : p.Positive) : 0 ≤ complementarity p := by
  rcases hp with ⟨hpx, hpw, hpy, hpz⟩
  unfold complementarity
  rw [dotProduct, dotProduct]
  exact add_nonneg
    (Finset.sum_nonneg (fun j _ => mul_nonneg (le_of_lt (hpz j)) (le_of_lt (hpx j))))
    (Finset.sum_nonneg (fun i _ => mul_nonneg (le_of_lt (hpy i)) (le_of_lt (hpw i))))
