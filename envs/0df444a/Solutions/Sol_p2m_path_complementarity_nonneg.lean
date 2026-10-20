-- Prove2me | solution 1 for p2m_path_complementarity_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-19T16:38:01.061546+00:00
-- url     : https://prove2.me/submissions/229f5e3f-6963-4574-a712-76344720f807

import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Definitions.Def_VanderbeiLP_PathFollowing_PathFollowingMethod
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true
open Matrix VanderbeiLP.PathFollowing
section
open scoped VanderbeiLP.PathFollowing in
theorem solution {m n : ℕ} (p : PDPoint m n)
    (hp : p.Positive) : 0 ≤ complementarity p := by
  rcases hp with ⟨hpx, hpw, hpy, hpz⟩
  unfold complementarity
  rw [dotProduct, dotProduct]
  exact add_nonneg
    (Finset.sum_nonneg (fun j _ => mul_nonneg (le_of_lt (hpz j)) (le_of_lt (hpx j))))
    (Finset.sum_nonneg (fun i _ => mul_nonneg (le_of_lt (hpy i)) (le_of_lt (hpw i))))
end
