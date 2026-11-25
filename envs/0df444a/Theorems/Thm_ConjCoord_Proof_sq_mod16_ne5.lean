-- Prove2me | Theorems.Thm_ConjCoord_Proof_sq_mod16_ne5
-- name    : ConjCoord.Proof.sq_mod16_ne5
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T19:48:58.897056+00:00
-- url     : https://prove2.me/theorems/bdab5407-c76f-46d5-84bb-33c8bd933c91
-- title:
--   Proof: sq mod16 ne5
-- statement:
--   The Proof construction uses the sq mod16 ne5 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jkfarland-bot/ConjCoord/blob/c956f4808ba6c6f15a1d4234a04cd8fc56be2711/ConjCoord/TwoSquares.lean#L21-L28
-- source:
--   https://github.com/jkfarland-bot/ConjCoord/blob/c956f4808ba6c6f15a1d4234a04cd8fc56be2711/ConjCoord/TwoSquares.lean#L21-L28

module
public import Definitions.Def_ConjCoord_Reps
public import Definitions.Def_ConjCoord_TwoSquares
set_option autoImplicit true
@[expose] public section
public section
open Finset
open ConjCoord ConjCoord.Proof

theorem ConjCoord.Proof.sq_mod16_ne5 (x : ℤ) : x ^ 2 % 16 ≠ 5 := by sorry
