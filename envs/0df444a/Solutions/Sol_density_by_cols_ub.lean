-- Prove2me | solution 1 for density_by_cols_ub
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T10:06:57.134549+00:00
-- url     : https://prove2.me/submissions/12fb526a-760e-49dc-8e18-19bf4e95aaa0

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
public import Theorems.Thm_split_density_to_cols
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
    (h_col_bounded : ∀ i, col_density M i ≤ c) : density M ≤ n * c := calc
      density M
  _ = ∑ i, col_density M i := split_density_to_cols M
  _ ≤ ∑ _, c := by gcongr; exact h_col_bounded _
  _ = n * c := by simp
