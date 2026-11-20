-- Prove2me | solution 1 for ex_identityPattern_two
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T10:10:00.154166+00:00
-- url     : https://prove2.me/submissions/dbc83cd6-abbb-41e4-834a-f4e40021af5c

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



set_option autoImplicit true
@[expose] public section
public section
open Finset Set
variable {α β : Type*} [LinearOrder α] [LinearOrder β]
theorem _root_.solution (n : ℕ) : ex (IdentityPattern 2) n = 2 * n - 1 := by
  obtain rfl | hn := eq_zero_or_neZero n
  · simp
  apply ge_antisymm
  · refine (le_ex_iff _ ⟨0, 0, by simp [IdentityPattern]⟩).2 ⟨(· = 0 ∨ · = 0), ?_, ?_⟩
    · rintro ⟨f, hf, g, hg, pmap⟩
      have hf₀ : f 1 ≠ 0 := (hf Fin.zero_lt_one).ne_bot
      have hg₀ : g 1 ≠ 0 := (hg Fin.zero_lt_one).ne_bot
      simpa [IdentityPattern, hf₀, hg₀] using pmap 1
    calc
          2 * n - 1
        = #(.Ioo (-n : ℤ) n) := by simp; omega
      _ ≤ #{(i, j) : Fin n × Fin n | i = 0 ∨ j = 0} := by
        refine card_le_card_of_forall_subsingleton (fun z (i, j) ↦ z = i.val - j.val) ?_ ?_
        · simp only [Finset.mem_Ioo, mem_filter, Finset.mem_univ, true_and, or_and_right,
            exists_or, Prod.exists, exists_and_left, exists_eq_left, Fin.coe_ofNat_eq_mod,
            Nat.zero_mod, Nat.cast_zero, zero_sub, ← neg_eq_iff_eq_neg, sub_zero, and_imp]
          rintro (z | z) hnz hzn
          · exact .inr ⟨⟨z, by simpa using hzn⟩, rfl⟩
          · exact .inl ⟨⟨z + 1, by simp [Int.negSucc_eq] at hnz; omega⟩, rfl⟩
        · aesop (add simp [Set.Subsingleton])
      _ = density _ := by rw [density_def]
  classical
  simp only [ex, Finset.sup_le_iff, mem_filter, Finset.mem_univ, true_and]
  intro M
  contrapose
  simp only [density, not_le]
  intro M_has_two_n_points
  let f : Fin n × Fin n → ℤ := fun ⟨i, j⟩ ↦ i - j
  let s := (filter (fun (i, j) ↦ M i j) univ)
  have : s.card > 2*n-1 := by aesop
  let t : Finset ℤ := Icc (-n + 1) (n - 1)
  have tcardeq2nm1 : t.card = 2*n -1 := by
    simp only [Int.card_Icc, sub_add_cancel, t]
    cases n
    · contradiction
    simp
    omega
  let k := 1
  have hf ⦃a⦄ (_ : a ∈ s) : f a ∈ t := by simp [f, t]; omega
  have hn : t.card * k < s.card := by
    simp only [Int.card_Icc, sub_add_cancel, mul_one, t, k, s]
    cases n
    · contradiction
    simp
    omega
  obtain ⟨y, hy, hy'⟩ := exists_lt_card_fiber_of_mul_lt_card_of_maps_to hf hn
  simp only [k] at hy'
  rw [one_lt_card] at hy'
  simp only [mem_filter, ne_eq] at hy'
  obtain ⟨a, ⟨ha, ha'⟩, b, ⟨hb, hb'⟩, hab⟩ := hy'
  have ⦃x⦄ (ha : x ∈ s) : M x.1 x.2 := by aesop
  have hmaa : M a.1 a.2 := by aesop
  have hmbb : M b.1 b.2 := by aesop
  have abneq : ¬ (a.1 = b.1 ∧ a.2 = b.2) := by aesop
  have dominance : (a.1 < b.1 ∧ a.2 < b.2) ∨ (a.1 > b.1 ∧ a.2 > b.2) := by
    rw [← ha'] at hb'
    simp only [f] at hb'
    rw [sub_eq_sub_iff_add_eq_add] at hb'
    omega
  simp only [Contains, Fin.forall_fin_two, Fin.isValue]
  match dominance with
  | .inl ⟨hab₁, hab₂⟩ =>
      exact ⟨![a.1, b.1], by simpa [StrictMono, Fin.forall_fin_two], ![a.2, b.2], by
      simpa [StrictMono, Fin.forall_fin_two], by simp [IdentityPattern, *]⟩
  | .inr ⟨hab₁, hab₂⟩ =>
      exact ⟨![b.1, a.1], by simpa [StrictMono, Fin.forall_fin_two], ![b.2, a.2], by
      simpa [StrictMono, Fin.forall_fin_two], by simp [IdentityPattern, *]⟩
