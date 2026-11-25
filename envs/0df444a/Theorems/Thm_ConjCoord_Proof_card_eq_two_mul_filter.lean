-- Prove2me | Theorems.Thm_ConjCoord_Proof_card_eq_two_mul_filter
-- name    : ConjCoord.Proof.card_eq_two_mul_filter
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T19:47:01.897994+00:00
-- url     : https://prove2.me/theorems/cc66792a-5cfd-4f46-ac2b-4f835f4722c8
-- title:
--   Proof: card eq two mul filter
-- statement:
--   A finset with a fixed-point-free involution exchanging `P` and `¬P` has twice as many
--   elements as its `P`-part.
--
--   Source: https://github.com/jkfarland-bot/ConjCoord/blob/c956f4808ba6c6f15a1d4234a04cd8fc56be2711/ConjCoord/Reps.lean#L55-L70
-- source:
--   https://github.com/jkfarland-bot/ConjCoord/blob/c956f4808ba6c6f15a1d4234a04cd8fc56be2711/ConjCoord/Reps.lean#L55-L70

module
public import Definitions.Def_ConjCoord_Defs
public import Definitions.Def_ConjCoord_Reps
set_option autoImplicit true
@[expose] public section
public section
open Finset
open ConjCoord ConjCoord.Proof

theorem ConjCoord.Proof.card_eq_two_mul_filter {α : Type*} (S : Finset α) (σ : α → α) (P : α → Prop)
    [DecidablePred P] (hS : ∀ x ∈ S, σ x ∈ S) (hσ : ∀ x ∈ S, σ (σ x) = x)
    (hP : ∀ x ∈ S, P (σ x) ↔ ¬ P x) : S.card = 2 * (S.filter P).card := by sorry
