-- Prove2me | solution 1 for suffices_triple
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T08:50:48.675517+00:00
-- url     : https://prove2.me/submissions/123e8ccb-2757-410c-8383-b09c6ad41362

import Mathlib.Algebra.Field.ZMod
import Mathlib.Algebra.GCDMonoid.Finset
import Mathlib.Algebra.GCDMonoid.Nat
import Mathlib.Algebra.Lie.Basic
import Mathlib.Algebra.Lie.Subalgebra
import Mathlib.Algebra.Lie.Submodule
import Mathlib.Algebra.Algebra.Subalgebra.Basic
import Definitions.Def_Polychromatic_PolychromNumber
import Definitions.Def_Polychromatic_FourThree_Theory

set_option autoImplicit true
open Finset
theorem _root_.solution
    (h : ∀ a b c : ℤ, 0 < a → a < b → b < c → HasPolychromColouring (Fin 3) {0, a, b, c}) :
    ∀ S : Finset ℤ, #S = 4 → Minimal (· ∈ S) 0 → HasPolychromColouring (Fin 3) S := by
  intro S hS hS'
  have : #(S.erase 0) = 3 := by rw [card_erase_of_mem hS'.1, hS]
  rw [card_eq_three] at this
  obtain ⟨a, b, c, hab, hac, hbc, hS0⟩ := this
  have : S = {0, a, b, c} := by rw [← insert_erase hS'.1, hS0]
  wlog hab : a < b generalizing a b
  · apply this b a
    all_goals grind
  wlog hac : a < c generalizing a c
  · apply this a c
    all_goals grind
  wlog hbc : b < c generalizing b c
  · apply this c b
    all_goals grind
  have : 0 ≤ a := hS'.le (by grind)
  grind
