-- Prove2me | solution 1 for d9ProtectionLeftSlope_first_event
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-08T14:55:57.187688+00:00
-- url     : https://prove2.me/submissions/b19fd3db-747f-4120-924f-45194b320c8f

import Mathlib
import Definitions.Def_NestedSeatAlloc_IntPolicy_Model
import Definitions.Def_d9LeftSlope
import Definitions.Def_d9ProtectionLeftSlope
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open NestedSeatAlloc.IntPolicy
theorem solution
    (f p x : ℕ → ℝ) (j : ℕ) (hj : 1 ≤ j) (s : ℝ) :
    d9ProtectionLeftSlope f p x j (j + 1) s =
      if p j ≤ s ∧ s < p j + x (j + 1) then
        d9LeftSlope f p x j (p j) - f (j + 1)
      else 0 := by
  cases j with
  | zero => omega
  | succ j => simp [d9ProtectionLeftSlope]
