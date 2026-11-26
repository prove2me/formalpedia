-- Prove2me | solution 1 for two_pow_poly_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T22:47:45.644187+00:00
-- url     : https://prove2.me/submissions/e6e0771c-ebde-46b4-af0c-efd07d27d694

import Definitions.Def_CARDB
import Mathlib.Data.Fintype.Prod
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Definitions.Def_CARDB_Asymptotics
import Theorems.Thm_add_succ_sq
import Theorems.Thm_two_mul_pow
import Theorems.Thm_le_two_pow_sub_three

set_option autoImplicit true
open Set TopologicalSpace
variable {α : Type*} [Fintype α] [DecidableEq α]
variable {x y : α}
theorem _root_.solution (n : ℕ) (hn : 10 ≤ n) : n ^ 2 + n ≤ 2 ^ (n - 2) := by
  induction n, hn using Nat.le_induction with
  | base => decide
  | succ k hk ih =>
    have : 2 ≤ k := le_trans (by decide : 2 ≤ 10) hk
    have hpow : 2 ^ (k + 1 - 2) = 2 * 2 ^ (k - 2) := by
      rw [show k + 1 - 2 = k - 2 + 1 by omega, pow_succ, two_mul_pow]
    rw [add_succ_sq, hpow]
    have hsmall : 2 * k + 2 ≤ 2 ^ (k - 2) := by
      have hk1 : k + 1 ≤ 2 ^ (k - 3) := le_two_pow_sub_three k hk
      have : 3 ≤ k := le_trans (by decide : 3 ≤ 10) hk
      have h2 : 2 ^ (k - 2) = 2 * 2 ^ (k - 3) := by
        rw [show k - 2 = k - 3 + 1 by omega, pow_succ, two_mul_pow]
      have hmul : 2 * (k + 1) ≤ 2 * 2 ^ (k - 3) := Nat.mul_le_mul_left 2 hk1
      have : 2 * (k + 1) = 2 * k + 2 := by ring
      rw [this] at hmul
      rwa [h2]
    have hsum := Nat.add_le_add ih hsmall
    have : 2 ^ (k - 2) + 2 ^ (k - 2) = 2 * 2 ^ (k - 2) := by
      rw [two_mul]
    exact hsum.trans_eq this
