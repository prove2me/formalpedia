-- Prove2me | solution 1 for frequently_in_finite_set
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T04:13:45.646309+00:00
-- url     : https://prove2.me/submissions/c42ad2de-e1aa-4b19-ad90-c01084f39c27

import Definitions.Def_AutomataTheory_Sequences_Basic
import Definitions.Def_AutomataTheory_Sequences_InfOcc

set_option autoImplicit true
open Function Set Prod Option Filter Stream'
open Classical
attribute [local instance_reducible] Stream'
theorem _root_.solution {X : Type*} [Finite X] {s : Set X} {xs : Stream' X} :
    (∃ᶠ k in atTop, xs k ∈ s) ↔ ∃ x ∈ s, ∃ᶠ k in atTop, xs k = x := by
  constructor
  · intro h_inf
    rw [Nat.frequently_atTop_iff_infinite] at h_inf
    have : Infinite (xs ⁻¹' s) := h_inf.to_subtype
    let rf := Set.restrictPreimage s xs
    obtain ⟨⟨x, h_x⟩, h_inf'⟩ := Finite.exists_infinite_fiber rf
    rw [← Set.infinite_range_iff (Subtype.val_injective.comp Subtype.val_injective)] at h_inf'
    simp [rf, Set.range, ← Nat.frequently_atTop_iff_infinite] at h_inf'
    use x ; simp [h_x]
    apply Frequently.mono h_inf'
    tauto
  · rintro ⟨x, h_x, h_inf⟩
    apply Frequently.mono h_inf
    intro k h_k ; simpa [h_k]
