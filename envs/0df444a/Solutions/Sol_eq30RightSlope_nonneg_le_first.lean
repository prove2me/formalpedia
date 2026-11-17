-- Prove2me | solution 1 for eq30RightSlope_nonneg_le_first
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-16T09:39:03.599465+00:00
-- url     : https://prove2.me/submissions/f10affaa-121d-46a9-adef-498e85b27d97

import Mathlib
import Definitions.Def_NestedSeatAlloc_IntPolicy_Model
import Definitions.Def_eq30RightSlope
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true
open NestedSeatAlloc.IntPolicy

theorem eq30RightSlope_nonneg_le_first
    (f p x : ℕ → ℝ)
    (hf_nonneg : ∀ i, 1 ≤ i → 0 ≤ f i)
    (hf_le_first : ∀ i, 1 ≤ i → f i ≤ f 1) :
    ∀ k s, 0 ≤ eq30RightSlope f p x k s ∧
      eq30RightSlope f p x k s ≤ f 1 := by
  have h1 := hf_nonneg 1 le_rfl
  have key : ∀ k, (∀ s, 0 ≤ eq30RightSlope f p x k s ∧ eq30RightSlope f p x k s ≤ f 1) ∧
      (∀ s, 0 ≤ eq30RightSlope f p x (k + 1) s ∧ eq30RightSlope f p x (k + 1) s ≤ f 1) := by
    intro k
    induction k with
    | zero =>
      refine ⟨fun s => ?_, fun s => ?_⟩
      · simp [eq30RightSlope, h1]
      · show 0 ≤ eq30RightSlope f p x 1 s ∧ eq30RightSlope f p x 1 s ≤ f 1
        rw [eq30RightSlope]
        split_ifs <;> simp [h1]
    | succ k ih =>
      refine ⟨ih.2, fun s => ?_⟩
      show 0 ≤ eq30RightSlope f p x (k + 2) s ∧ eq30RightSlope f p x (k + 2) s ≤ f 1
      rw [eq30RightSlope]
      split_ifs
      · exact ih.2 s
      · exact ⟨hf_nonneg _ (by omega), hf_le_first _ (by omega)⟩
      · exact ih.2 _
  exact fun k s => (key k).1 s

theorem solution
    (f p x : ℕ → ℝ)
    (hf_nonneg : ∀ i, 1 ≤ i → 0 ≤ f i)
    (hf_le_first : ∀ i, 1 ≤ i → f i ≤ f 1) :
    ∀ k s, 0 ≤ eq30RightSlope f p x k s ∧
      eq30RightSlope f p x k s ≤ f 1 := by
  have h1 := hf_nonneg 1 le_rfl
  have key : ∀ k, (∀ s, 0 ≤ eq30RightSlope f p x k s ∧ eq30RightSlope f p x k s ≤ f 1) ∧
      (∀ s, 0 ≤ eq30RightSlope f p x (k + 1) s ∧ eq30RightSlope f p x (k + 1) s ≤ f 1) := by
    intro k
    induction k with
    | zero =>
      refine ⟨fun s => ?_, fun s => ?_⟩
      · simp [eq30RightSlope, h1]
      · show 0 ≤ eq30RightSlope f p x 1 s ∧ eq30RightSlope f p x 1 s ≤ f 1
        rw [eq30RightSlope]
        split_ifs <;> simp [h1]
    | succ k ih =>
      refine ⟨ih.2, fun s => ?_⟩
      show 0 ≤ eq30RightSlope f p x (k + 2) s ∧ eq30RightSlope f p x (k + 2) s ≤ f 1
      rw [eq30RightSlope]
      split_ifs
      · exact ih.2 s
      · exact ⟨hf_nonneg _ (by omega), hf_le_first _ (by omega)⟩
      · exact ih.2 _
  exact fun k s => (key k).1 s


