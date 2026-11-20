-- Prove2me | solution 1 for den_all1_matrix_row_subset
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T10:08:45.918836+00:00
-- url     : https://prove2.me/submissions/3dcfc781-c8b4-44d4-8ec2-40effdba6345

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
theorem _root_.solution {n : ℕ} (I : Finset (Fin n)) :
    let M (i j : Fin n) : Prop := (i, j) ∈ I ×ˢ Finset.univ
    density M = n * #I := by
  simp only [density, Prod.mk.eta]
  convert (Finset.card_product I (.univ : Finset <| Fin n)).trans _
  · ext
    simp
  · simp [mul_comm]
