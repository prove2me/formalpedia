-- Prove2me | solution 1 for le_two_pow_sub_three
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T22:47:05.59458+00:00
-- url     : https://prove2.me/submissions/1b18801f-2298-4abc-a852-b0834473277c

import Definitions.Def_CARDB
import Mathlib.Data.Fintype.Prod
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Definitions.Def_CARDB_Asymptotics
import Theorems.Thm_two_mul_pow

set_option autoImplicit true
open Set TopologicalSpace
variable {α : Type*} [Fintype α] [DecidableEq α]
variable {x y : α}
theorem _root_.solution (k : ℕ) (hk : 10 ≤ k) : k + 1 ≤ 2 ^ (k - 3) := by
  induction k, hk using Nat.le_induction with
  | base => decide
  | succ k hk ih =>
    have : 3 ≤ k := le_trans (by decide : 3 ≤ 10) hk
    have h2 : 2 ^ (k + 1 - 3) = 2 * 2 ^ (k - 3) := by
      rw [show k + 1 - 3 = k - 3 + 1 by omega, pow_succ, two_mul_pow]
    rw [h2]
    have : k + 2 ≤ 2 * (k + 1) := by nlinarith
    exact this.trans (Nat.mul_le_mul_left 2 ih)
