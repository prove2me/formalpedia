-- Prove2me | solution 1 for eq30_revenue_succ_eq_nextPayoff
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-08T15:44:38.487774+00:00
-- url     : https://prove2.me/submissions/d8e924ae-8a85-4a9d-9756-e427eb51a200

import Mathlib
import Definitions.Def_NestedSeatAlloc_IntPolicy_Model
import Definitions.Def_eq30NextPayoff
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true
open NestedSeatAlloc.IntPolicy
theorem solution
    (f p x : ℕ → ℝ) (j : ℕ) (s : ℝ) :
    revenue f p x (j + 2) s =
      eq30NextPayoff (fun t => revenue f p x (j + 1) t)
        (p (j + 1)) (x (j + 2)) (f (j + 2)) s := by
  rfl
