-- Prove2me | solution 1 for ex_identityPattern_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T10:11:17.56067+00:00
-- url     : https://prove2.me/submissions/ca556b0e-bd22-416d-ad18-40bc7c1b054f

module
public import Definitions.Def_ForbiddenMatrix_SmallPatterns
public import Mathlib.Algebra.Group.End
public import Mathlib.Data.Nat.Choose.Basic
public import Definitions.Def_ForbiddenMatrix_Mathlib_Data_ZMod_Basic
public import Mathlib.Combinatorics.Pigeonhole
public import Mathlib.Data.Finset.Sort
public import Mathlib.Data.Int.Interval
public import Mathlib.Tactic.Group
public import Mathlib.Tactic.Qify
public import Definitions.Def_ForbiddenMatrix_PermutationPatterns
public import Theorems.Thm_permPattern_one
public import Theorems.Thm_permPattern_refl
public import Theorems.Thm_Fin_natCast_val_eq_zmodFinEquiv
public import Theorems.Thm_card_rectPtSet
public import Theorems.Thm_card_rectPtsetSubsetMatrix
public import Theorems.Thm_contains_of_isEmpty
public import Theorems.Thm_ex_identityPattern_two
public import Theorems.Thm_ex_zero
attribute [local simp] Fin.natCast_val_eq_zmodFinEquiv
attribute [local simp] card_rectPtSet
attribute [local simp] card_rectPtsetSubsetMatrix
attribute [local simp] contains_of_isEmpty
attribute [local simp] ex_identityPattern_two
attribute [local simp] ex_zero


attribute [local simp] permPattern_one
attribute [local simp] permPattern_refl

set_option autoImplicit true
@[expose] public section
public section
open Finset Set OrderDual Equiv
variable {k n q : ℕ}
theorem _root_.solution (k n : ℕ) : ex (IdentityPattern k) n ≤ (2 * n - 1) * (k - 1) := by
  obtain rfl | hn := eq_zero_or_neZero n
  · simp
  classical
  simp only [ex, Finset.sup_le_iff, mem_filter, Finset.mem_univ, true_and]
  intro M avoid_Ik
  by_contra! M_large_density
  let d : Fin n × Fin n → ℤ := fun ⟨i, j⟩ ↦ i - j
  let s : Finset (Fin n × Fin n) := {(i, j) : Fin n × Fin n | M i j}
  let t : Finset ℤ := Icc (-n + 1) (n - 1)
  obtain ⟨p, hp, hp'⟩ : ∃ p ∈ t, k - 1 < #{x ∈ s | d x = p} := by
    apply exists_lt_card_fiber_of_mul_lt_card_of_maps_to
    · simp [s, d, t]
      grind
    convert! M_large_density
    simp [t]
    lia
  let fiber : Finset (Fin n × Fin n) := {x ∈ s | d x = p}
  let fiberSnd : Finset (Fin n) := {x.2 | x ∈ fiber}
  have card_fiber : #fiber = #fiberSnd := by apply card_bij fun a _ ↦ a.2 <;> aesop
  have le_card_fiberSnd : k ≤ #fiberSnd := by simp [← card_fiber, fiber]; lia
  let g := fiberSnd.orderEmbOfCardLe le_card_fiberSnd
  let f (i : Fin k) : Fin n := (ZMod.finEquiv n).symm p + g i
  have f_spec a (a' : Fin n) (ha : a' - g a = p) : f a = a' := by simp [f, ← ha]
  have mono_f : StrictMono f := fun a b hab ↦ by
    have hga : g a ∈ fiberSnd := fiberSnd.orderEmbOfCardLe_mem _ a
    have hgb : g b ∈ fiberSnd := fiberSnd.orderEmbOfCardLe_mem _ b
    simp only [mem_filter, Prod.exists, exists_eq_right, Finset.mem_univ, true_and, fiberSnd, fiber,
      d] at hga hgb
    obtain ⟨a', -, ha'⟩ := hga
    obtain ⟨b', -, hb'⟩ := hgb
    have hgab : g a < g b := by simpa
    have hab' : a' < b' := by grind
    simpa [f_spec _ _ ha', f_spec _ _ hb'] using hab'
  refine avoid_Ik ⟨f, mono_f, g, by simp [StrictMono], ?_⟩
  simp only [IdentityPattern, forall_eq']
  intro a
  have hga : g a ∈ fiberSnd := fiberSnd.orderEmbOfCardLe_mem _ a
  simp only [mem_filter, Finset.mem_univ, true_and, Prod.exists, exists_eq_right, fiberSnd, fiber,
    d, s] at hga
  obtain ⟨a', hfa', ha'⟩ := hga
  simpa [f_spec _ _ ha'] using hfa'
