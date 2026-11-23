-- Prove2me | solution 1 for leads_to_cases
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T04:41:46.957869+00:00
-- url     : https://prove2.me/submissions/392e40f3-fe25-463e-8adb-e2f67f5540c1

import Definitions.Def_AutomataTheory_Sequences_Basic
import Definitions.Def_AutomataTheory_Sequences_Temporal

set_option autoImplicit true
open Function Set Filter Stream'
variable {X : Type*} {xs : Stream' X}
theorem _root_.solution {p q r s : Set X}
    (h1 : LeadsTo xs (p ∩ q) r) (h2 : LeadsTo xs (p ∩ qᶜ) s) : LeadsTo xs p (r ∪ s) := by
  intro k h_p
  rcases Classical.em (xs k ∈ q) with h_q | h_not_q
  · let h_pq : xs k ∈ p ∩ q := by tauto
    obtain ⟨k', h_k', h_r⟩ := h1 k h_pq
    use k' ; simp [h_k', h_r]
  . let h_pq : xs k ∈ p ∩ qᶜ := by tauto
    obtain ⟨k', h_k', h_s⟩ := h2 k h_pq
    use k' ; simp [h_k', h_s]
