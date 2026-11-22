-- Prove2me | solution 1 for suffices_gcd
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T08:50:52.139772+00:00
-- url     : https://prove2.me/submissions/71a5897b-8991-495d-84cd-277dd82de085

import Mathlib.Algebra.Field.ZMod
import Mathlib.Algebra.GCDMonoid.Finset
import Mathlib.Algebra.GCDMonoid.Nat
import Mathlib.Algebra.Lie.Basic
import Mathlib.Algebra.Lie.Subalgebra
import Mathlib.Algebra.Lie.Submodule
import Mathlib.Algebra.Algebra.Subalgebra.Basic
import Definitions.Def_Polychromatic_PolychromNumber
import Definitions.Def_Polychromatic_FourThree_Theory
import Theorems.Thm_gcd_pos
import Theorems.Thm_hasPolychromColouring_neg
import Theorems.Thm_hasPolychromColouring_univ
import Theorems.Thm_le_polychromNumber_iff_hasPolychromColouring
import Theorems.Thm_polychromNumber_pair
import Theorems.Thm_polychromNumber_singleton
import Theorems.Thm_polychromNumber_univ
import Theorems.Thm_polychromNumber_zsmul
attribute [local simp] hasPolychromColouring_neg
attribute [local simp] hasPolychromColouring_univ
attribute [local simp] polychromNumber_pair
attribute [local simp] polychromNumber_singleton
attribute [local simp] polychromNumber_univ



set_option autoImplicit true
open Finset
theorem _root_.solution
    (h : ∀ a b c : ℤ, 0 < a → a < b → a + b ≤ c → Finset.gcd {a, b, c} id = 1 →
      HasPolychromColouring (Fin 3) {0, a, b, c}) :
    ∀ a b c : ℤ, 0 < a → a < b → a + b ≤ c →
      HasPolychromColouring (Fin 3) {0, a, b, c} := by
  intro a b c ha hab hbc
  let d := Finset.gcd {a, b, c} id
  obtain hd | hd := eq_or_ne d 1
  · exact h a b c ha hab hbc hd
  have hd₀ : 0 < d := gcd_pos ⟨a, by simp, ha.ne'⟩
  let a' := a / d
  let b' := b / d
  let c' := c / d
  have h' : ({a', b', c'} : Finset ℤ) = ({a, b, c} : Finset ℤ).image (fun x ↦ x / d) := by
    simp [a', b', c']
  have : Finset.gcd {a', b', c'} id = 1 := by
    rw [h', ← Finset.gcd_eq_gcd_image]
    exact Finset.gcd_div_eq_one (α := ℤ) (i := a) (by simp) ha.ne'
  have h'' : ({a, b, c} : Finset ℤ) = ({a', b', c'} : Finset ℤ).image (d • ·) := by
    rw [h', image_image, image_congr, image_id]
    intro i hi
    simp only [Finset.mem_coe] at hi
    dsimp
    rw [Int.mul_ediv_cancel']
    apply Finset.gcd_dvd hi
  have : ({0, a, b, c} : Finset ℤ) = ({0, a', b', c'} : Finset ℤ).image (d • ·) := by
    rw [image_insert, smul_zero, h'']
  rw [this]
  rw [← le_polychromNumber_iff_hasPolychromColouring (by simp), polychromNumber_zsmul hd₀.ne',
    le_polychromNumber_iff_hasPolychromColouring (by simp)]
  refine h _ _ _
    (Int.ediv_pos_of_pos_of_dvd ha hd₀.le (Finset.gcd_dvd (by simp)))
    ?_ ?_ ‹_›
  · simp only [a', b']
    rw [Int.ediv_lt_ediv_iff_of_dvd_of_pos hd₀ hd₀, mul_comm]
    · gcongr
    · apply Finset.gcd_dvd (by simp)
    · apply Finset.gcd_dvd (by simp)
  · simp only [a', b', c']
    rw [← Int.add_ediv_of_dvd_left]
    swap
    · exact Finset.gcd_dvd (by simp)
    apply Int.ediv_le_ediv hd₀ hbc
