-- Prove2me | solution 1 for suffices_flip
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T08:50:49.10849+00:00
-- url     : https://prove2.me/submissions/ea43070a-3dff-433a-ada9-418514c419b3

import Mathlib.Algebra.Field.ZMod
import Mathlib.Algebra.GCDMonoid.Finset
import Mathlib.Algebra.GCDMonoid.Nat
import Mathlib.Algebra.Lie.Basic
import Mathlib.Algebra.Lie.Subalgebra
import Mathlib.Algebra.Lie.Submodule
import Mathlib.Algebra.Algebra.Subalgebra.Basic
import Definitions.Def_Polychromatic_PolychromNumber
import Definitions.Def_Polychromatic_FourThree_Theory
import Theorems.Thm_hasPolychromColouring_neg
import Theorems.Thm_hasPolychromColouring_univ
import Theorems.Thm_polychromNumber_pair
import Theorems.Thm_polychromNumber_singleton
import Theorems.Thm_polychromNumber_univ
attribute [local simp] hasPolychromColouring_neg
attribute [local simp] hasPolychromColouring_univ
attribute [local simp] polychromNumber_pair
attribute [local simp] polychromNumber_singleton
attribute [local simp] polychromNumber_univ



set_option autoImplicit true
open Finset
theorem _root_.solution
    (h : ∀ a b c : ℤ, 0 < a → a < b → a + b ≤ c →
      HasPolychromColouring (Fin 3) {0, a, b, c}) :
    ∀ a b c : ℤ, 0 < a → a < b → b < c → HasPolychromColouring (Fin 3) {0, a, b, c} := by
  intro a b c ha hab hbc
  by_cases hsum : a + b ≤ c
  · exact h a b c ha hab hsum
  rw [← hasPolychromColouring_neg, ← hasPolychromColouring_vadd (n := c)]
  suffices HasPolychromColouring (Fin 3) {0, c - b, c - a, c} by
    simp only [neg_insert, neg_zero, neg_singleton, vadd_finset_insert, vadd_eq_add, add_zero,
      ← sub_eq_add_neg, vadd_finset_singleton, sub_self]
    convert this using 1
    grind
  grind
