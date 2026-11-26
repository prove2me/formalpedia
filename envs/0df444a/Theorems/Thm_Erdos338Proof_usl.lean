-- Prove2me | Theorems.Thm_Erdos338Proof_usl
-- name    : Erdos338Proof.usl
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T00:59:41.016664+00:00
-- url     : https://prove2.me/theorems/8f55b21b-814d-4d15-b4ea-b2a1c0b4d13d
-- title:
--   Erdos338 Proof: usl
-- statement:
--   The Erdos338 Proof construction uses the usl property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/veljjanoski/erdos338-palomar/blob/a699263d0f7cdce0e5b3026bce86eab30973d0f8/Erdos338/Shift.lean#L21-L177
-- source:
--   https://github.com/veljjanoski/erdos338-palomar/blob/a699263d0f7cdce0e5b3026bce86eab30973d0f8/Erdos338/Shift.lean#L21-L177

module
public import Definitions.Def_Erdos338_Structure
public import Definitions.Def_Erdos338_Shift
set_option autoImplicit true
@[expose] public section
public section
open Finset
open Erdos338Proof

theorem Erdos338Proof.usl {γ : ℝ} (hγ : 0 < γ) : ∃ K : ℕ, ∀ M : Set ℕ, (∃ N, ∀ b ≥ N, γ * b ≤ cnt M b) →
    ∃ d b₀ N', 1 ≤ d ∧ d ≤ K ∧ ∀ x ≥ N', ∃ Ms : Multiset ℕ, Multiset.card Ms = K ∧
      (∀ a ∈ Ms, a ∈ M) ∧ Ms.sum = K * b₀ + d * x := by sorry
