-- Prove2me | solution 1 for suffices_nat
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T08:51:24.255209+00:00
-- url     : https://prove2.me/submissions/7e072f8f-2262-48ea-8d7c-80be84c9f8c8

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
theorem _root_.solution (C : ℕ) (h : allC C) :
    ∀ a b c : ℤ, 0 < a → a < b → a + b ≤ c → c < C → Finset.gcd {a, b, c} id = 1 →
      HasPolychromColouring (Fin 3) {0, a, b, c} := by
  intro a b c ha hab hbc hcc hgcd
  lift a to ℕ using by grind
  lift b to ℕ using by grind
  lift c to ℕ using by grind
  simp only [gcd_insert, id_eq, gcd_singleton, Int.normalize_coe_nat, ← Int.coe_gcd,
    Int.gcd_natCast_natCast, Nat.cast_eq_one] at hgcd
  exact h c (by grind) b (by grind) (by grind) a (by grind) (by grind) (by grind) (by grind) hgcd
