-- Prove2me | solution 1 for split_density
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T10:08:44.550177+00:00
-- url     : https://prove2.me/submissions/96ec0b7c-23f2-45c1-8a8f-4937abe2ff8f

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
theorem _root_.solution {n : ℕ} (M : Fin n → Fin n → Prop) (Pred : Fin n → Fin n → Prop) :
    let M1 (i j : Fin n) : Prop := M i j ∧  (Pred i j);
    let M2 (i j : Fin n) : Prop := M i j ∧ ¬ (Pred i j);
    density M = density M1 + density M2 := by
  classical
  let M1 (i j : Fin n) : Prop := M i j ∧  (Pred i j);
  let M2 (i j : Fin n) : Prop := M i j ∧ ¬ (Pred i j);
  let s1 : Finset (Fin n × Fin n) := {(i, j) | M1 i j}
  let s2 : Finset (Fin n × Fin n) := {(i, j) | M2 i j}
  let s : Finset (Fin n × Fin n) := {(i, j) | M  i j}
  have seqs1s2 : s = s1 ∪ s2 := by
    ext x
    constructor
    · -- (->)
      intro xins
      simp [s] at xins
      simp [s1, s2, M1, M2]
      tauto
    · -- (<-)
      intro xins1s2
      simp [s1, s2, M1, M2] at xins1s2
      simp [s]
      tauto
  have dm : density M = s.card := by simp [density, s]
  have dm1 : density M1 = #s1 := by simp [density_def, s1]
  have dm2 : density M2 = #s2 := by simp [density_def, s2]
  have s1eqs2card : (s1 ∪ s2).card = s1.card + s2.card := by
    apply card_union_of_disjoint
    rw [disjoint_left]
    aesop
  rw [← seqs1s2] at s1eqs2card
  aesop
