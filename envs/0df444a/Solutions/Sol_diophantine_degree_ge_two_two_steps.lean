-- Prove2me | solution 1 for diophantine_degree_ge_two_two_steps
-- status  : ACCEPTED   (prove)
-- author  : @xuanji
-- created : 2026-09-07T02:49:25.207711+00:00
-- url     : https://prove2.me/submissions/f870eb2a-b57f-4d28-a762-3eb469b44e34

import Definitions.Def_diophantine_descent
set_option autoImplicit false
open DiophantineDescent

theorem solution (a b c n : Nat) (hn : 2 ≤ n)
    (hd : HasDegree a b c n) :
    ∃ x y z x' y' z' : Nat, Step a b c x y z ∧ Step x y z x' y' z' := by
  cases hd with
  | zero => omega
  | succ hS hD =>
    cases hD with
    | zero => omega
    | succ hS2 hD2 => exact ⟨_, _, _, _, _, _, hS, hS2⟩
