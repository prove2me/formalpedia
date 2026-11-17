-- Prove2me | solution 1 for d9Revenue_update_protection_hasDerivWithinAt_eq_below
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-16T09:42:59.129093+00:00
-- url     : https://prove2.me/submissions/b5fa7575-8672-4936-ab5c-7f324105d611

import Mathlib
import Definitions.Def_NestedSeatAlloc_IntPolicy_Model
import Theorems.Thm_d9Revenue_update_protection_eq_below
open NestedSeatAlloc.IntPolicy

theorem d9Revenue_update_protection_hasDerivWithinAt_eq_below
    (f p x : ℕ → ℝ) (j k : ℕ) (s : ℝ) (hkj : k ≤ j) :
    HasDerivWithinAt
      (fun u => revenue f (Function.update p j u) x k s)
      0 (Set.Ici (p j)) (p j) := by
  have h : (fun u => revenue f (Function.update p j u) x k s) = fun _ => revenue f p x k s :=
    funext fun u => d9Revenue_update_protection_eq_below f p x j k u s hkj
  rw [h]
  exact hasDerivWithinAt_const _ _ _

theorem solution
    (f p x : ℕ → ℝ) (j k : ℕ) (s : ℝ) (hkj : k ≤ j) :
    HasDerivWithinAt
      (fun u => revenue f (Function.update p j u) x k s)
      0 (Set.Ici (p j)) (p j) := by
  have h : (fun u => revenue f (Function.update p j u) x k s) = fun _ => revenue f p x k s :=
    funext fun u => d9Revenue_update_protection_eq_below f p x j k u s hkj
  rw [h]
  exact hasDerivWithinAt_const _ _ _


