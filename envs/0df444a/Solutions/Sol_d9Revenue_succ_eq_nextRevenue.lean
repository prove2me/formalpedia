-- Prove2me | solution 1 for d9Revenue_succ_eq_nextRevenue
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-08T12:35:05.047208+00:00
-- url     : https://prove2.me/submissions/47e16f0d-3b4e-44ba-b234-54aafa59d40a

import Mathlib
import Definitions.Def_NestedSeatAlloc_IntPolicy_Model
import Definitions.Def_d9NextRevenue
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open NestedSeatAlloc.IntPolicy
theorem solution
    (f p x : ℕ → ℝ) (j : ℕ) (s : ℝ) :
    revenue f p x (j + 2) s =
      d9NextRevenue (fun t => revenue f p x (j + 1) t)
        (p (j + 1)) (x (j + 2)) (f (j + 2)) s := by
  by_cases hprotection : s < p (j + 1)
  · simp [d9NextRevenue, revenue, hprotection]
  · by_cases hcapacity : s < p (j + 1) + x (j + 2)
    · simp [d9NextRevenue, revenue, hprotection, hcapacity]
    · simp [d9NextRevenue, revenue, hprotection, hcapacity]
