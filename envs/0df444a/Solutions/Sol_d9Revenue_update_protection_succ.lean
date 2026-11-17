-- Prove2me | solution 1 for d9Revenue_update_protection_succ
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-16T09:40:40.964622+00:00
-- url     : https://prove2.me/submissions/f75e578d-9c5f-4023-aef8-c8ce9e4f9283

import Mathlib
import Definitions.Def_NestedSeatAlloc_IntPolicy_Model
import Definitions.Def_d9NextRevenue
import Theorems.Thm_d9Revenue_succ_eq_nextRevenue
import Theorems.Thm_d9Revenue_eq_of_policy_agree_below
open NestedSeatAlloc.IntPolicy

theorem d9Revenue_update_protection_succ
    (f p x : ℕ → ℝ) (j : ℕ) (u s : ℝ) (hj : 1 ≤ j) :
    revenue f (Function.update p j u) x (j + 1) s =
      d9NextRevenue (fun t => revenue f p x j t) u
        (x (j + 1)) (f (j + 1)) s := by
  obtain ⟨i, rfl⟩ : ∃ i, j = i + 1 := ⟨j - 1, by omega⟩
  show revenue f (Function.update p (i + 1) u) x (i + 2) s = _
  rw [d9Revenue_succ_eq_nextRevenue, Function.update_self]
  have hfun : (fun t => revenue f (Function.update p (i + 1) u) x (i + 1) t) =
      fun t => revenue f p x (i + 1) t := by
    funext t
    exact d9Revenue_eq_of_policy_agree_below f _ p x (i + 1)
      (fun k _ hk => Function.update_of_ne (by omega) _ _) t
  rw [hfun]

theorem solution
    (f p x : ℕ → ℝ) (j : ℕ) (u s : ℝ) (hj : 1 ≤ j) :
    revenue f (Function.update p j u) x (j + 1) s =
      d9NextRevenue (fun t => revenue f p x j t) u
        (x (j + 1)) (f (j + 1)) s := by
  obtain ⟨i, rfl⟩ : ∃ i, j = i + 1 := ⟨j - 1, by omega⟩
  show revenue f (Function.update p (i + 1) u) x (i + 2) s = _
  rw [d9Revenue_succ_eq_nextRevenue, Function.update_self]
  have hfun : (fun t => revenue f (Function.update p (i + 1) u) x (i + 1) t) =
      fun t => revenue f p x (i + 1) t := by
    funext t
    exact d9Revenue_eq_of_policy_agree_below f _ p x (i + 1)
      (fun k _ hk => Function.update_of_ne (by omega) _ _) t
  rw [hfun]


