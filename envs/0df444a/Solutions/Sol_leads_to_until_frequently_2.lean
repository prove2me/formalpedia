-- Prove2me | solution 1 for leads_to_until_frequently_2
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T04:42:16.4798+00:00
-- url     : https://prove2.me/submissions/16b3d219-3f2d-44b5-91b5-edd2b9b6e6e4

import Definitions.Def_AutomataTheory_Sequences_Basic
import Definitions.Def_AutomataTheory_Sequences_Temporal

set_option autoImplicit true
open Function Set Filter Stream'
variable {X : Type*} {xs : Stream' X}
theorem _root_.solution {p q : Set X}
    (h1 : Step xs (p ∩ qᶜ) p) (h2 : ∃ᶠ k in atTop, xs k ∈ q) : LeadsTo xs p (p ∩ q) := by
  intro k h_p
  by_contra! h_not_pq
  have h_p_not_q : ∀ k' ≥ k, xs k' ∈ p ∩ qᶜ := by
    intro k' h_k'
    simp [le_iff_exists_add] at h_k'
    obtain ⟨n, h_k'⟩ := h_k'
    revert k' h_k'
    induction' n with n h_ind <;> intro k' h_k' <;> simp [h_k']
    · have h_not_pq' := h_not_pq k (by omega)
      tauto
    have h_n := h_ind (k + n) (rfl)
    have h_n_p := h1 (k + n) h_n
    have h_n_q := h_not_pq (k + n + 1) (by omega)
    simp [h_n_p] at h_n_q
    simp [← add_assoc] ; tauto
  rw [frequently_atTop] at h2
  obtain ⟨k', h_k', h_q'⟩ := h2 k
  have := (h_p_not_q k' h_k').2
  contradiction
