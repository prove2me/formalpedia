-- Prove2me | solution 1 for option_some_pigeonhole
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T04:32:02.99648+00:00
-- url     : https://prove2.me/submissions/bd424071-625c-47b3-93fa-81317d3fdf25

import Definitions.Def_AutomataTheory_Mathlib_Imports
import Definitions.Def_AutomataTheory_Sequences_Basic

set_option autoImplicit true
open Function Set Option Stream'
theorem _root_.solution {X : Type*} [Finite X] {n : ℕ} (f : Fin n → Option X)
    (h : {j | (f j).isSome}.ncard > Nat.card X) :
    ∃ j1 j2, j1 ≠ j2 ∧ ∃ x, f j1 = some x ∧ f j2 = some x := by
  have ht : (some '' (univ : Set X)).Finite := by exact toFinite (some '' univ)
  have : (some '' (univ : Set X)).ncard = Nat.card X := by
    rw [ncard_image_of_injective (univ : Set X) (some_injective X)] ; exact ncard_univ X
  have hc : (some '' (univ : Set X)).ncard < {j | (f j).isSome}.ncard := by omega
  have hf : ∀ j ∈ {j | (f j).isSome}, f j ∈ some '' (univ : Set X) := by
    intro j ; simp ; rw [isSome_iff_exists] ; tauto
  obtain ⟨j1, h_j1, j2, h_j2, h_ne, h_eq⟩ := exists_ne_map_eq_of_ncard_lt_of_maps_to hc hf ht
  obtain ⟨s1, h_s1⟩ := isSome_iff_exists.mp h_j1
  obtain ⟨s2, h_s2⟩ := isSome_iff_exists.mp h_j2
  simp [h_s1, h_s2] at h_eq ; obtain ⟨rfl⟩ := h_eq
  use j1, j2 ; simp [h_ne] ; use s1
