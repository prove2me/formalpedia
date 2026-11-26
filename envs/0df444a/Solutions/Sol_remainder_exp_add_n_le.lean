-- Prove2me | solution 1 for remainder_exp_add_n_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T22:48:23.258792+00:00
-- url     : https://prove2.me/submissions/1c2dd42e-564e-4610-8c63-dab7e445edbd

import Definitions.Def_CARDB
import Mathlib.Data.Fintype.Prod
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Definitions.Def_CARDB_Asymptotics
import Theorems.Thm_two_pow_poly_le

set_option autoImplicit true
open Set TopologicalSpace
variable {α : Type*} [Fintype α] [DecidableEq α]
variable {x y : α}
open Filter Topology
theorem _root_.solution (n : ℕ) (hn : 10 ≤ n) :
    n * (n - 1) + 3 * 2 ^ (n - 2) + n ≤ 2 ^ n - n := by
  have hpoly := two_pow_poly_le n hn
  have hsq : n * (n - 1) + n = n ^ 2 := by
    rw [Nat.mul_sub_one, Nat.sub_add_cancel (Nat.le_mul_self n), sq]
  have h4 : 2 ^ (n - 2) + 3 * 2 ^ (n - 2) = 2 ^ n := by
    have : 2 ^ (n - 2) + 3 * 2 ^ (n - 2) = 4 * 2 ^ (n - 2) := by ring
    have hfour : (4 : ℕ) = 2 ^ 2 := by decide
    rw [this, hfour, ← pow_add, show 2 + (n - 2) = n by omega]
  have : n ^ 2 + 3 * 2 ^ (n - 2) + n ≤ 2 ^ n := by
    have := Nat.add_le_add hpoly (Nat.le_refl (3 * 2 ^ (n - 2)))
    convert this using 1
    · ring
    · exact h4.symm
  have hleft : n * (n - 1) + 3 * 2 ^ (n - 2) + n + n = n ^ 2 + 3 * 2 ^ (n - 2) + n := by
    rw [← hsq]; ac_rfl
  have : n * (n - 1) + 3 * 2 ^ (n - 2) + n + n ≤ 2 ^ n := by
    rwa [hleft]
  exact Nat.le_sub_of_add_le this
