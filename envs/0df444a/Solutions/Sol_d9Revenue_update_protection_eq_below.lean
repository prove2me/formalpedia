-- Prove2me | solution 1 for d9Revenue_update_protection_eq_below
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-08T12:36:15.624236+00:00
-- url     : https://prove2.me/submissions/c8f3dceb-a3df-4332-8907-6d7eff4ff364

import Mathlib
import Definitions.Def_NestedSeatAlloc_IntPolicy_Model
import Theorems.Thm_d9Revenue_eq_of_policy_agree_below
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open NestedSeatAlloc.IntPolicy
theorem solution
    (f p x : ℕ → ℝ) (j k : ℕ) (u s : ℝ) (hkj : k ≤ j) :
    revenue f (Function.update p j u) x k s = revenue f p x k s := by
  apply d9Revenue_eq_of_policy_agree_below f (Function.update p j u) p x k
  intro i hi hik
  have hij : i < j := lt_of_lt_of_le hik hkj
  rw [Function.update_of_ne (ne_of_lt hij) u p]
