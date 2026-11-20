-- Prove2me | solution 1 for le_ex_iff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T10:05:18.203388+00:00
-- url     : https://prove2.me/submissions/cb6fa5fb-eb27-415f-a915-644d39eb9dea

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
public import Theorems.Thm_contains_of_isEmpty
public import Theorems.Thm_not_contains_false
attribute [local simp] contains_of_isEmpty


attribute [local gcongr] density_mono
attribute [local simp] ex_zero

set_option autoImplicit true
@[expose] public section
public section
open Finset
variable {α β γ δ : Type*} [LinearOrder α] [LinearOrder β] [LinearOrder γ] [LinearOrder δ] {m n : ℕ}
  {P : α → β → Prop}
theorem _root_.solution (P : α → β → Prop) (P_nonempty : ∃ a b, P a b) {m n : ℕ} :
    m ≤ ex P n ↔ ∃ (M : Fin n → Fin n → Prop), ¬ Contains P M ∧ m ≤ density M := by
  obtain rfl | hm := eq_zero_or_pos m
  · simpa using ⟨_, not_contains_false P P_nonempty⟩
  · simp [ex, Finset.le_sup_iff hm]
