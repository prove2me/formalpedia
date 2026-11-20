-- Prove2me | solution 1 for density_mk_mem_product
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T10:08:45.478926+00:00
-- url     : https://prove2.me/submissions/5e62b9a7-1b1b-487f-99b3-35c1352173da

module
public import Definitions.Def_ScoutForbiddenMatrixContainment
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Data.Finset.Lattice.Fold
public import Mathlib.Data.Fintype.Prod
public import Mathlib.Order.Interval.Finset.Nat
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Algebra.Order.Monoid.Canonical.Basic
public import Definitions.Def_ForbiddenMatrix_ExtremalFunction
public import Theorems.Thm_density_def
public import Theorems.Thm_density_mono
public import Theorems.Thm_ex_zero
public import Theorems.Thm_card_rectPtSet
public import Theorems.Thm_card_rectPtsetSubsetMatrix
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
theorem _root_.solution {n : ℕ} (I J : Finset (Fin n)) :
    density (fun i j ↦ (i, j) ∈ I ×ˢ J) = #I * #J := by simp [density_def, -mem_product]
