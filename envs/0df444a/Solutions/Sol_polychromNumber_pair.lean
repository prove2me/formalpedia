-- Prove2me | solution 1 for polychromNumber_pair
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T08:45:15.067747+00:00
-- url     : https://prove2.me/submissions/802f7b60-4303-4eb4-b9f1-6985a027fdc7

import Definitions.Def_Polychromatic_Colouring
import Definitions.Def_Polychromatic_PolychromNumber
import Theorems.Thm_polychromNumber_vadd
import Theorems.Thm_polychromNumber_singleton
import Theorems.Thm_polychromNumber_univ
import Theorems.Thm_polychromNumber_image_injective
import Theorems.Thm_hasPolychromColouring_neg
import Theorems.Thm_hasPolychromColouring_univ
attribute [local simp] hasPolychromColouring_neg
attribute [local simp] hasPolychromColouring_univ


attribute [local simp] polychromNumber_singleton
attribute [local simp] polychromNumber_univ
section
variable {G : Type*} [AddCommGroup G] {S : Finset G} {K : Type*}
open Finset Fintype Pointwise
private lemma polychromNumber_pair_aux_ℤ :
    polychromNumber ({0, 1} : Finset ℤ) = 2 := by
  set S : Finset ℤ := {0, 1}
  refine le_antisymm ?easy ?hard
  case easy =>
    have : #S = 2 := by simp [S]
    rw [← this]
    exact polychromNumber_le_card
  case hard =>
    suffices HasPolychromColouring (ZMod 2) S by
      simpa using card_le_polychromNumber this
    refine ⟨Int.castAddHom (ZMod 2), ?_⟩
    have : S.image (Int.castAddHom (ZMod 2)) = Finset.univ := rfl
    rw [isPolychrom_iff_mem_image]
    simp_rw [Finset.image_vadd_distrib, this]
    simp
private lemma polychromNumber_pair_aux [DecidableEq G] [IsAddTorsionFree G] {x : G} (hx : x ≠ 0) :
    polychromNumber {0, x} = 2 := by
  have : Function.Injective (zmultiplesHom G x) := by
    simpa [zmultiplesHom] using not_isOfFinAddOrder_of_isAddTorsionFree hx
  rw [← polychromNumber_pair_aux_ℤ, ← polychromNumber_image_injective _ this]
  simp
section Int
example : polychromNumber (G := ℤ) {0, 1, 5} = 3 := by
  set S : Finset ℤ := {0, 1, 5}
  refine le_antisymm ?easy ?hard
  case easy =>
    calc
      polychromNumber S ≤ #S := polychromNumber_le_card
      _ = 3 := by simp [S]
  case hard =>
    suffices HasPolychromColouring (ZMod 3) S by simpa using card_le_polychromNumber this
    refine ⟨Int.castAddHom (ZMod 3), ?_⟩
    have : S.image (Int.castAddHom (ZMod 3)) = Finset.univ := by decide
    rw [isPolychrom_iff_mem_image]
    simp_rw [Finset.image_vadd_distrib, this]
    simp
end Int
end

set_option autoImplicit true
variable {G : Type*} [AddCommGroup G] {S : Finset G} {K : Type*}
open Finset Fintype Pointwise
theorem _root_.solution [DecidableEq G] [IsAddTorsionFree G] {x y : G} (hxy : x ≠ y) :
    polychromNumber {x, y} = 2 := by
-- ANCHOR_END: polychromNumber_pair
  have := polychromNumber_pair_aux (x := y - x) (by simpa [sub_eq_zero, eq_comm] using hxy)
  rwa [← polychromNumber_vadd (n := x), Finset.vadd_finset_insert, Finset.vadd_finset_singleton,
    vadd_eq_add, add_zero, vadd_eq_add, add_sub_cancel] at this
