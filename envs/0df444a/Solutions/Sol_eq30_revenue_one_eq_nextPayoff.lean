-- Prove2me | solution 1 for eq30_revenue_one_eq_nextPayoff
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-08T16:10:15.514925+00:00
-- url     : https://prove2.me/submissions/72fb6fbb-4d73-481c-b2f2-49013e265cf4

import Mathlib
import Definitions.Def_NestedSeatAlloc_IntPolicy_Model
import Definitions.Def_eq30NextPayoff
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true
open NestedSeatAlloc.IntPolicy
theorem solution
    (f p x : ℕ → ℝ) (s : ℝ) (hs : 0 ≤ s) :
    revenue f p x 1 s =
      eq30NextPayoff (fun _ => 0) 0 (x 1) (f 1) s := by
  have hs0 : ¬ s < 0 := not_lt_of_ge hs
  by_cases hsx : s < x 1
  · simp [revenue, eq30NextPayoff, hs0, hsx] <;> ring
  · have hx : x 1 ≤ s := le_of_not_gt hsx
    simp [revenue, eq30NextPayoff, hs0, hsx] <;> ring
