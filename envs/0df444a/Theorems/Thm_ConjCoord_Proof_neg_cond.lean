-- Prove2me | Theorems.Thm_ConjCoord_Proof_neg_cond
-- name    : ConjCoord.Proof.neg_cond
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T19:49:46.78469+00:00
-- url     : https://prove2.me/theorems/10916723-debc-5058-a724-510895e369ec
-- title:
--   Proof: neg cond
-- statement:
--   The Proof construction uses the neg cond property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jkfarland-bot/ConjCoord/blob/c956f4808ba6c6f15a1d4234a04cd8fc56be2711/ConjCoord/TwoSquares.lean#L107-L108
-- source:
--   https://github.com/jkfarland-bot/ConjCoord/blob/c956f4808ba6c6f15a1d4234a04cd8fc56be2711/ConjCoord/TwoSquares.lean#L107-L108

module
public import Definitions.Def_ConjCoord_Reps
public import Definitions.Def_ConjCoord_TwoSquares
set_option autoImplicit true
@[expose] public section
public section
open Finset
open ConjCoord ConjCoord.Proof

theorem ConjCoord.Proof.neg_cond (β : ℤ) : ((-β) % 16 = 6 ∨ (-β) % 16 = 10) ↔ (β % 16 = 6 ∨ β % 16 = 10) := by sorry
