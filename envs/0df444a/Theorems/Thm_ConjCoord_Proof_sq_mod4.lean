-- Prove2me | Theorems.Thm_ConjCoord_Proof_sq_mod4
-- name    : ConjCoord.Proof.sq_mod4
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T19:46:24.25808+00:00
-- url     : https://prove2.me/theorems/543d2325-5043-5f0f-a541-2ee86421c07a
-- title:
--   Proof: sq mod4
-- statement:
--   The Proof construction uses the sq mod4 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jkfarland-bot/ConjCoord/blob/c956f4808ba6c6f15a1d4234a04cd8fc56be2711/ConjCoord/Reps.lean#L48-L51
-- source:
--   https://github.com/jkfarland-bot/ConjCoord/blob/c956f4808ba6c6f15a1d4234a04cd8fc56be2711/ConjCoord/Reps.lean#L48-L51

module
public import Definitions.Def_ConjCoord_Defs
public import Definitions.Def_ConjCoord_Reps
set_option autoImplicit true
@[expose] public section
public section
open Finset
open ConjCoord ConjCoord.Proof

theorem ConjCoord.Proof.sq_mod4 (x : ℤ) : (Even x ∧ x ^ 2 % 4 = 0) ∨ (Odd x ∧ x ^ 2 % 4 = 1) := by sorry
