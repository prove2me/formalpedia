-- Prove2me | solution 1 for le_ex_self_of_two_points
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T10:11:08.240592+00:00
-- url     : https://prove2.me/submissions/55c16e14-cbbf-4187-92e3-a225eadb5b1e

module
public import Definitions.Def_ScoutForbiddenMatrixContainment
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Data.Finset.Lattice.Fold
public import Mathlib.Data.Fintype.Prod
public import Mathlib.Order.Interval.Finset.Nat
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Algebra.Order.Monoid.Canonical.Basic
public import Definitions.Def_ForbiddenMatrix_ExtremalFunction
public import Theorems.Thm_density_mono
public import Theorems.Thm_ex_zero
public import Theorems.Thm_le_ex_iff
public import Theorems.Thm_card_rectPtSet
public import Theorems.Thm_card_rectPtsetSubsetMatrix
public import Theorems.Thm_den_all1_matrix_single_row
public import Theorems.Thm_den_all1_matrix_single_col
public import Theorems.Thm_contains_of_isEmpty
attribute [local simp] contains_of_isEmpty


attribute [local gcongr] density_mono
attribute [local simp] ex_zero
attribute [local simp] card_rectPtSet
attribute [local simp] card_rectPtsetSubsetMatrix

set_option autoImplicit true
@[expose] public section
public section
open Finset
variable {α β γ δ : Type*} [LinearOrder α] [LinearOrder β] [LinearOrder γ] [LinearOrder δ] {m n : ℕ}
  {P : α → β → Prop}
theorem _root_.solution (P : α → β → Prop) (n : ℕ)
    (hP : ∃ x y : (α × β), P x.1 x.2 ∧ P y.1 y.2 ∧ x ≠ y) : n ≤ ex P n := by
  obtain rfl | n_pos := eq_zero_or_neZero n
  · simp
  simp only [ne_eq, Prod.ext_iff, not_and_or] at hP
  obtain ⟨⟨a₁, b₁⟩, ⟨a₂, b₂⟩, h₁, h₂, ha | hb⟩ := hP
  · refine (le_ex_iff _ ⟨_, _, h₁⟩).2 ⟨fun i j ↦ i = 0, ?_, by simp [den_all1_matrix_single_row]⟩
    rintro ⟨f, hf, g, hg, hfg⟩
    exact ha <| hf.injective <| (hfg _ _ h₁).trans (hfg _ _ h₂).symm
  · refine (le_ex_iff _ ⟨_, _, h₁⟩).2 ⟨fun i j ↦ j = 0, ?_, by simp [den_all1_matrix_single_col]⟩
    rintro ⟨f, hf, g, hg, hfg⟩
    exact hb <| hg.injective <| (hfg _ _ h₁).trans (hfg _ _ h₂).symm
