-- Prove2me | Theorems.Thm_ConjCoord_Proof_card_eq_three
-- name    : ConjCoord.Proof.card_eq_three
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T19:46:50.115174+00:00
-- url     : https://prove2.me/theorems/489c8048-1ded-4da8-bb64-cbeca60f6e2e
-- title:
--   Proof: card eq three
-- statement:
--   Splitting a count according to which of three exclusive and exhaustive conditions holds.
--
--   Source: https://github.com/jkfarland-bot/ConjCoord/blob/c956f4808ba6c6f15a1d4234a04cd8fc56be2711/ConjCoord/Reps.lean#L73-L80
-- source:
--   https://github.com/jkfarland-bot/ConjCoord/blob/c956f4808ba6c6f15a1d4234a04cd8fc56be2711/ConjCoord/Reps.lean#L73-L80

module
public import Definitions.Def_ConjCoord_Defs
public import Definitions.Def_ConjCoord_Reps
set_option autoImplicit true
@[expose] public section
public section
open Finset
open ConjCoord ConjCoord.Proof

theorem ConjCoord.Proof.card_eq_three {α : Type*} (S : Finset α) (P Q R : α → Prop) [DecidablePred P]
    [DecidablePred Q] [DecidablePred R]
    (h : ∀ x ∈ S, (P x ∧ ¬ Q x ∧ ¬ R x) ∨ (¬ P x ∧ Q x ∧ ¬ R x) ∨ (¬ P x ∧ ¬ Q x ∧ R x)) :
    S.card = (S.filter P).card + (S.filter Q).card + (S.filter R).card := by sorry
