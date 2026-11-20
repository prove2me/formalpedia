-- Prove2me | solution 1 for den_all1_matrix_column_interval
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T10:09:55.011971+00:00
-- url     : https://prove2.me/submissions/fcaed127-e320-4cfb-9be7-b375c6559464

module
public import Definitions.Def_ScoutForbiddenMatrixContainment
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Data.Finset.Lattice.Fold
public import Mathlib.Data.Fintype.Prod
public import Mathlib.Order.Interval.Finset.Nat
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Algebra.Order.Monoid.Canonical.Basic
public import Definitions.Def_ForbiddenMatrix_ExtremalFunction
public import Theorems.Thm_card_interval
public import Theorems.Thm_den_all1_matrix_col_subset

set_option autoImplicit true
@[expose] public section
public section
open Finset
variable {α β γ δ : Type*} [LinearOrder α] [LinearOrder β] [LinearOrder γ] [LinearOrder δ] {m n : ℕ}
  {P : α → β → Prop}
theorem _root_.solution {n : ℕ} (a b : Fin n) :
    let I := ({x | ↑x ∈ Finset.Icc a.1 b.1} : Finset (Fin n))
    let M (i j : Fin n) : Prop := (i, j) ∈ Finset.univ ×ˢ I
    density M = n * (b + 1 - a) := by
  extract_lets I M
  have h1 : #I = #(.Icc a.1 b.1) := by
    apply card_interval
    exact b.2
  observe h2 : #(.Icc a.1 b.1) = b.1 +1 - a.1
  calc
    density M = n * #I := by exact den_all1_matrix_col_subset I
    _ = n * #(.Icc a.1 b.1) := by exact congrArg (HMul.hMul n) h1
    _ = n * (b + 1 - a) := by exact congrArg (HMul.hMul n) h2
