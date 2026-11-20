-- Prove2me | solution 1 for density_by_rows_ub
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T10:06:56.438314+00:00
-- url     : https://prove2.me/submissions/2fbc9c78-14fa-45df-b1f2-eca0c3a7d6b3

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
public import Theorems.Thm_split_density_to_rows
public import Theorems.Thm_contains_of_isEmpty
attribute [local simp] contains_of_isEmpty


attribute [local gcongr] density_mono
attribute [local simp] ex_zero

set_option autoImplicit true
@[expose] public section
public section
open Finset
variable {α β γ δ : Type*} [LinearOrder α] [LinearOrder β] [LinearOrder γ] [LinearOrder δ] {m n : ℕ}
  {P : α → β → Prop}
theorem _root_.solution {n c : ℕ} (M : Fin n → Fin n → Prop)
    (h_row_density_bounded : ∀ i, row_density M i ≤ c) : density M ≤ n * c := calc
    density M
  _ = ∑ i, row_density M i := split_density_to_rows M
  _ ≤ ∑ _, c := by gcongr; exact h_row_density_bounded _
  _ = n * c := by simp
