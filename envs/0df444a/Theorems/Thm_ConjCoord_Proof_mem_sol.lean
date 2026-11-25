-- Prove2me | Theorems.Thm_ConjCoord_Proof_mem_sol
-- name    : ConjCoord.Proof.mem_sol
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T19:46:21.523967+00:00
-- url     : https://prove2.me/theorems/7ee67b06-0be6-5c43-ae23-4f8e4993c2b7
-- title:
--   Proof: mem sol
-- statement:
--   The Proof construction uses the mem sol property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jkfarland-bot/ConjCoord/blob/c956f4808ba6c6f15a1d4234a04cd8fc56be2711/ConjCoord/Reps.lean#L31-L46
-- source:
--   https://github.com/jkfarland-bot/ConjCoord/blob/c956f4808ba6c6f15a1d4234a04cd8fc56be2711/ConjCoord/Reps.lean#L31-L46

module
public import Definitions.Def_ConjCoord_Defs
public import Definitions.Def_ConjCoord_Reps
set_option autoImplicit true
@[expose] public section
public section
open Finset
open ConjCoord ConjCoord.Proof

theorem ConjCoord.Proof.mem_sol {a b c n : ℕ} (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (v : ℤ × ℤ × ℤ) :
    v ∈ sol a b c n ↔ (a : ℤ) * v.1 ^ 2 + b * v.2.1 ^ 2 + c * v.2.2 ^ 2 = n := by sorry
