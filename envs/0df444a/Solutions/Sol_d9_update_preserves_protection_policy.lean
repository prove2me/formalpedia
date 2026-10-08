-- Prove2me | solution 1 for d9_update_preserves_protection_policy
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-08T08:48:04.719966+00:00
-- url     : https://prove2.me/submissions/1590ba18-b983-43e7-b73f-0355d4288c0b

import Mathlib
import Definitions.Def_NestedSeatAlloc_IntPolicy_Model
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open NestedSeatAlloc.IntPolicy
theorem solution
    (p : ℕ → ℝ) (j : ℕ) (u : ℝ)
    (hp : IsProtectionPolicy p) (hu : 0 ≤ u) :
    IsProtectionPolicy (Function.update p j u) := by
  intro i hi
  simp only [Function.update_apply]
  by_cases hEq : i = j
  · subst i
    simpa using hu
  · simpa [hEq] using hp i hi
