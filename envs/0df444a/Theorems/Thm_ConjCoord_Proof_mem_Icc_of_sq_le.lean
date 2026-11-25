-- Prove2me | Theorems.Thm_ConjCoord_Proof_mem_Icc_of_sq_le
-- name    : ConjCoord.Proof.mem_Icc_of_sq_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T19:46:42.154138+00:00
-- url     : https://prove2.me/theorems/f51d6b28-a341-5eb2-9d33-d4d5e815bd03
-- title:
--   Proof: mem Icc of sq le
-- statement:
--   The Proof construction uses the mem Icc of sq le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jkfarland-bot/ConjCoord/blob/c956f4808ba6c6f15a1d4234a04cd8fc56be2711/ConjCoord/Reps.lean#L25-L29
-- source:
--   https://github.com/jkfarland-bot/ConjCoord/blob/c956f4808ba6c6f15a1d4234a04cd8fc56be2711/ConjCoord/Reps.lean#L25-L29

module
public import Definitions.Def_ConjCoord_Defs
public import Definitions.Def_ConjCoord_Reps
set_option autoImplicit true
@[expose] public section
public section
open Finset
open ConjCoord ConjCoord.Proof

theorem ConjCoord.Proof.mem_Icc_of_sq_le {x : ℤ} {n : ℕ} (h : x ^ 2 ≤ n) : x ∈ Icc (-(n : ℤ)) n := by sorry
