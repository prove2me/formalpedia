-- Prove2me | solution 1 for ex_verticalPattern_two
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T10:10:50.668614+00:00
-- url     : https://prove2.me/submissions/2b41989c-c729-49c1-b2ef-a4c831befc46

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
public import Theorems.Thm_density_def
public import Theorems.Thm_ex_zero
public import Theorems.Thm_le_ex_iff
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
theorem _root_.solution (n : ℕ) : ex (VerticalPattern 2) n = n := by
  classical
  refine le_antisymm ?_ ?_
  · simp only [ex, Finset.sup_le_iff, mem_filter, Finset.mem_univ, true_and]
    intro M
    contrapose
    simp only [density, not_le]
    intro more_than_n
    let f : Fin n × Fin n → ℕ := fun ⟨i, j⟩ ↦ j
    let s := (filter (fun (i, j) ↦ M i j) univ)
    have : s.card > n := by aesop
    let t : Finset ℕ := Finset.Iio n
    let k := 1
    have hf ⦃a⦄ (_ : a ∈ s) : f a ∈ t := by simp [f, t]
    have hn : t.card * k < s.card := by aesop
    obtain ⟨y, hy, hy'⟩ := exists_lt_card_fiber_of_mul_lt_card_of_maps_to hf hn
    simp only [k] at hy'
    rw [one_lt_card] at hy'
    simp only [mem_filter, ne_eq] at hy'
    obtain ⟨a, ha, b, hb, hab⟩ := hy'
    obtain ⟨ha, ha'⟩ := ha
    obtain ⟨hb, hb'⟩ := hb
    rw [Contains]
    have : a.2 = b.2 := by
      simp only [f] at ha' hb'
      rw [← ha'] at hb'
      omega
    have dominance : a.1 < b.1 ∨ b.1 < a.1 := by grind
    let g := ![a.2]
    have gmono : StrictMono g := by simp [StrictMono]
    cases dominance with
    | inl ab =>
      refine ⟨![a.1, b.1], by  simpa [f, StrictMono, Fin.forall_fin_two], g, gmono, ?_⟩
      simp [Fin.forall_fin_two, AllPattern, g]
      aesop
    | inr ba =>
      let f := ![b.1, a.1]
      refine ⟨![b.1, a.1], by  simpa [f, StrictMono, Fin.forall_fin_two], g, gmono, ?_⟩
      simp [Fin.forall_fin_two, AllPattern, g]
      aesop
  · obtain rfl | hn := eq_zero_or_neZero n
    · simp
    refine (le_ex_iff _ ⟨0, by simp [AllPattern]⟩).2 ⟨fun i j ↦ i = 0, ?_, ge_of_eq ?_⟩
    · rintro ⟨f, hf, g, hg, prop⟩
      simp only [AllPattern, forall_const, Fin.forall_fin_two, Fin.isValue] at prop
      exact (hf Fin.zero_lt_one).ne <| prop.1.trans prop.2.symm
    · calc  density _
        _ = #{x : Fin n × Fin n | x.1 = 0} := density_def _
        _ = #({0} ×ˢ .univ : Finset <| Fin n × Fin n) := by congr; aesop
        _ = n := by simp
