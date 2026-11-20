-- Prove2me | solution 1 for ex_horizontal
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T10:10:50.16255+00:00
-- url     : https://prove2.me/submissions/0a888829-dfee-4c54-8cd2-6c0f9cd2dee6

module
public import Definitions.Def_ForbiddenMatrix_ExtremalFunction
public import Mathlib.Data.Fin.VecNotation
public import Definitions.Def_ForbiddenMatrix_MatrixOperations
public import Mathlib.Algebra.Order.Monoid.Canonical.Basic
public import Mathlib.Combinatorics.Enumerative.DoubleCounting
public import Mathlib.Combinatorics.Pigeonhole
public import Mathlib.Data.Finset.Sort
public import Mathlib.Data.Int.Interval
public import Mathlib.Logic.Equiv.Fin.Basic
public import Definitions.Def_ForbiddenMatrix_SmallPatterns
public import Theorems.Thm_ex_identityPattern_two
public import Theorems.Thm_card_rectPtSet
public import Theorems.Thm_card_rectPtsetSubsetMatrix
public import Theorems.Thm_contains_of_isEmpty
public import Theorems.Thm_density_by_rows_ub
public import Theorems.Thm_ex_zero
attribute [local simp] card_rectPtSet
attribute [local simp] card_rectPtsetSubsetMatrix
attribute [local simp] contains_of_isEmpty
attribute [local simp] ex_zero


attribute [local simp] ex_identityPattern_two

set_option autoImplicit true
@[expose] public section
public section
open Finset Set
variable {α β : Type*} [LinearOrder α] [LinearOrder β]
theorem _root_.solution (k n : ℕ) : ex (HorizontalPattern k) n ≤ n*(k-1) := by
  classical
  simp only [ex, Finset.sup_le_iff, mem_filter, Finset.mem_univ, true_and]
  intro M NoHPk
  refine density_by_rows_ub M fun i ↦ ?_
  contrapose! NoHPk
  simp [row_density] at NoHPk
  let s : Finset (Fin n) := {j | M i j}
  have h : k ≤ s.card := by simp [s]; omega
  let g := s.orderEmbOfCardLe h
  simp only [Contains, Fin.forall_fin_one, Fin.isValue]
  refine ⟨![i], by simp [StrictMono], g, by simp [StrictMono, OrderEmbedding.lt_iff_lt], ?_⟩
  simp only [Fin.isValue, AllPattern, Matrix.cons_val_fin_one, forall_const]
  intro j
  simpa [s] using s.orderEmbOfCardLe_mem h j
