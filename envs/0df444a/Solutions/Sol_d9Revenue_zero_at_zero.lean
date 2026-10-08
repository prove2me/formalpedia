-- Prove2me | solution 1 for d9Revenue_zero_at_zero
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-08T08:37:32.414025+00:00
-- url     : https://prove2.me/submissions/fa9b1a35-e654-49a0-b661-470d24265c7f

import Mathlib
import Definitions.Def_NestedSeatAlloc_IntPolicy_Model
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open NestedSeatAlloc.IntPolicy
theorem solution
    (f p x : ℕ → ℝ)
    (hp : ∀ i, 1 ≤ i → 0 ≤ p i)
    (hx : ∀ i, 0 ≤ x i) :
    ∀ k, revenue f p x k 0 = 0 := by
  intro k
  induction k using Nat.twoStepInduction with
  | zero => simp [revenue]
  | one =>
      by_cases hzero : x 1 = 0
      · simp [revenue, hzero]
      · have hpos : 0 < x 1 := lt_of_le_of_ne (hx 1) (Ne.symm hzero)
        simp [revenue, hpos]
  | more n ih0 ih1 =>
      have hprev : revenue f p x (n + 1) 0 = 0 := ih1
      by_cases hzero : p (n + 1) = 0
      · by_cases hxzero : x (n + 2) = 0
        · simp [revenue, hzero, hxzero, hprev]
        · have hxpos : 0 < x (n + 2) :=
            lt_of_le_of_ne (hx (n + 2)) (Ne.symm hxzero)
          simp [revenue, hzero, hxpos, hprev]
      · have hppos : 0 < p (n + 1) :=
          lt_of_le_of_ne (hp (n + 1) (by omega)) (Ne.symm hzero)
        simp [revenue, hppos, hprev]
