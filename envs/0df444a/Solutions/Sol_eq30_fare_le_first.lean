-- Prove2me | solution 1 for eq30_fare_le_first
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-08T10:15:16.521501+00:00
-- url     : https://prove2.me/submissions/7e421c4a-e187-40b8-a074-03d4ef079b14

import Mathlib
import Definitions.Def_NestedSeatAlloc_IntPolicy_Model
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true
open NestedSeatAlloc.IntPolicy
theorem solution
    (f : ℕ → ℝ) (hanti : ∀ k, 1 ≤ k → f (k + 1) < f k) :
    ∀ i, 1 ≤ i → f i ≤ f 1 := by
  have hshift : ∀ n, f (n + 1) ≤ f 1 := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
        have hstrict := hanti (n + 1) (by omega)
        have hstep : f (n + 2) < f (n + 1) := by simpa using hstrict
        exact le_trans (le_of_lt hstep) ih
  intro i hi
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : i ≠ 0)
  exact hshift n
