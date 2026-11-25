-- Prove2me | Theorems.Thm_ConjCoord_Proof_gCount_eq_card
-- name    : ConjCoord.Proof.gCount_eq_card
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T19:50:17.723903+00:00
-- url     : https://prove2.me/theorems/da5c86ad-1cfe-4a39-af79-96878dc93d6a
-- title:
--   Proof: g Count eq card
-- statement:
--   The Proof construction uses the g Count eq card property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jkfarland-bot/ConjCoord/blob/c956f4808ba6c6f15a1d4234a04cd8fc56be2711/ConjCoord/TwoSquares.lean#L93-L93
-- source:
--   https://github.com/jkfarland-bot/ConjCoord/blob/c956f4808ba6c6f15a1d4234a04cd8fc56be2711/ConjCoord/TwoSquares.lean#L93-L93

module
public import Definitions.Def_ConjCoord_Reps
public import Definitions.Def_ConjCoord_TwoSquares
set_option autoImplicit true
@[expose] public section
public section
open Finset
open ConjCoord ConjCoord.Proof

theorem ConjCoord.Proof.gCount_eq_card (m : ℕ) : gCount m = (gset m).card := by sorry
