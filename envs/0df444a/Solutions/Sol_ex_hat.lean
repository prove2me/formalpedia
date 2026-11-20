-- Prove2me | solution 1 for ex_hat
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T10:11:26.376551+00:00
-- url     : https://prove2.me/submissions/c9c49ca5-85f4-48bf-82db-3f9cd187f04d

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
public import Theorems.Thm_ex_verticalPattern_two
public import Theorems.Thm_ex_horizontal
public import Theorems.Thm_card_rectPtSet
public import Theorems.Thm_card_rectPtsetSubsetMatrix
public import Theorems.Thm_contains_of_isEmpty
public import Theorems.Thm_density_le_ex_of_not_contains
public import Theorems.Thm_ex_zero
public import Theorems.Thm_split_density
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
theorem _root_.solution (n : ℕ) : ex HatPattern n ≤ 3 * n := by
  classical
  simp only [ex, Finset.sup_le_iff, mem_filter, Finset.mem_univ, true_and]
  intro M noHat
  let min_or_max_of_row := fun i j ↦ (∀ j', M i j' → j ≤ j') ∨ (∀ j', M i j' → j' ≤ j)
  let M1 (i j : Fin n) : Prop := M i j ∧ (min_or_max_of_row i j)
  let M2 (i j : Fin n) : Prop := M i j ∧ ¬ (min_or_max_of_row i j)
  have M1_avoids_H3 : ¬ Contains (HorizontalPattern 3) M1 := by
    rintro ⟨f, _, g, g_mono, prop⟩
    simp only [AllPattern, forall_const, Fin.forall_fin_one, Fin.isValue] at prop
    -- prop :
    -- M1   g(0) g(1) g(2)
    -- f(0) 1   1   1
    simp only [Fin.isValue, M1] at prop
    obtain ⟨_, h_min_max_g1⟩ : M (f 0) (g 1) ∧ min_or_max_of_row (f 0) (g 1) := prop 1
    -- since g(1) in M1, g(1) is either min or max
    cases h_min_max_g1 with
     | inl g1_min =>
      have : g 1 ≤ g 0 := by aesop (add simp g1_min)
      have : g 0 < g 1 := by aesop (add simp g_mono)
      omega
     | inr g1_max =>
      have : g 2 ≤ g 1 := by aesop (add simp g1_max)
      have : g 1 < g 2 := by aesop (add simp g_mono)
      omega
  have M2_avoids_V2 : ¬ Contains (VerticalPattern 2) M2 := by
    rintro ⟨f, hf, g, _, v2_to_M2⟩
    simp only [AllPattern, not_or, not_forall, not_le, forall_const, Fin.forall_fin_one,
      Fin.isValue, Fin.forall_fin_two, M2, min_or_max_of_row] at v2_to_M2
    obtain ⟨⟨hib, -, -⟩, -, ⟨a, hja, hab⟩, c, hjc, hbc⟩ := v2_to_M2
    set b := g 0
    --      a b c
    -- f(0)   1
    -- f(1) 1   1
    exact noHat ⟨f, hf, ![a, b, c], by simp [StrictMono, Fin.forall_fin_succ, *, hab.trans hbc], by
      simp [HatPattern, Fin.forall_fin_succ, *]⟩
  have dm1 := calc
        density M1
    _ ≤ ex (HorizontalPattern 3) n := density_le_ex_of_not_contains M1 M1_avoids_H3
    _ ≤ n * 2 := ex_horizontal 3 n
  have dm2 := calc
        density M2
    _ ≤ ex (VerticalPattern 2) n := density_le_ex_of_not_contains M2 M2_avoids_V2
    _ = n := ex_verticalPattern_two n
  calc
        density M
    _ = density M1 + density M2 := split_density M min_or_max_of_row
    _ ≤ n * 2 + density M2 := by simp [dm1]
    _ ≤ n * 2 + n := by simp [dm2]
    _ ≤ 3 * n := by omega
