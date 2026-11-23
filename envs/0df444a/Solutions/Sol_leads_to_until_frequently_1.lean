-- Prove2me | solution 1 for leads_to_until_frequently_1
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T04:41:55.027994+00:00
-- url     : https://prove2.me/submissions/8f6885e0-3411-410d-a1d7-ffffcb91962e

import Definitions.Def_AutomataTheory_Sequences_Basic
import Definitions.Def_AutomataTheory_Sequences_Temporal

set_option autoImplicit true
open Function Set Filter Stream'
variable {X : Type*} {xs : Stream' X}
theorem _root_.solution {p q : Set X}
    (h1 : Step xs (p ∩ qᶜ) p) (h2 : ∃ᶠ k in atTop, xs k ∉ p) : LeadsTo xs p q := by
  intro k h_p
  by_contra! h_q
  have h_p' : ∀ k' ≥ k, xs k' ∈ p := by
    intro k' h_k'
    simp [le_iff_exists_add] at h_k'
    obtain ⟨n, h_k'⟩ := h_k'
    revert k' h_k'
    induction' n with n h_ind <;> intro k' h_k' <;> simp [h_k']
    · assumption
    have h_pq_n : xs (k + n) ∈ p ∩ qᶜ := by
      have h_q_n := h_q (k + n) (by omega)
      simp [h_q_n]
      exact h_ind (k + n) (rfl)
    exact h1 (k + n) h_pq_n
  rw [frequently_atTop] at h2
  obtain ⟨k', h_k', h_not_p⟩ := h2 k
  have := h_p' k' h_k'
  contradiction
