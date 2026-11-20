-- Prove2me | solution 1 for ex_vertical
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T10:11:25.673167+00:00
-- url     : https://prove2.me/submissions/f964a18b-e18c-47dc-bdb4-c96dc9044b10

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
public import Theorems.Thm_ex_horizontal
public import Theorems.Thm_card_rectPtSet
public import Theorems.Thm_card_rectPtsetSubsetMatrix
public import Theorems.Thm_contains_of_isEmpty
public import Theorems.Thm_density_le_ex_of_not_contains
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
theorem _root_.solution (k n : ℕ) : ex (VerticalPattern k) n ≤ n*(k-1) := by
  classical
  calc
    ex (VerticalPattern k) n
    _ ≤ ex ( tranpose (VerticalPattern k)) n := ?exv
    _ = ex ( HorizontalPattern k) n := by rfl
    _ ≤ n*(k-1) := ex_horizontal k n
  case exv =>
    simp only [ex, Finset.sup_le_iff, mem_filter, Finset.mem_univ, true_and]
    intro M hM
    rw [← ex]
    let M' := tranpose M
    have hM' : ¬ Contains (tranpose (VerticalPattern k)) M' := by
      by_contra H
      obtain ⟨f, hf, g, hg, emb_pat_to_M'⟩ := H
      have : Contains (VerticalPattern k) M := by
        refine ⟨g, hg, f, hf, by
          intro a b
          apply emb_pat_to_M'
        ⟩
      contradiction
    have dmeqdm' : density M = density M' :=
      Finset.card_equiv (Equiv.prodComm ..) fun _ ↦ by simp; rfl
    calc
      density M = density M' := dmeqdm'
      _        ≤ ex (tranpose (VerticalPattern k)) n := (density_le_ex_of_not_contains M' hM')
