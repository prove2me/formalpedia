-- Prove2me | Theorems.Thm_ConjCoord_Proof_mem_sol111
-- name    : ConjCoord.Proof.mem_sol111
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T19:46:34.627805+00:00
-- url     : https://prove2.me/theorems/d1bbf6bd-95e5-51e3-a177-f67c19cc6ab8
-- title:
--   Proof: mem sol111
-- statement:
--   The Proof construction uses the mem sol111 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jkfarland-bot/ConjCoord/blob/c956f4808ba6c6f15a1d4234a04cd8fc56be2711/ConjCoord/Reps.lean#L86-L88
-- source:
--   https://github.com/jkfarland-bot/ConjCoord/blob/c956f4808ba6c6f15a1d4234a04cd8fc56be2711/ConjCoord/Reps.lean#L86-L88

module
public import Definitions.Def_ConjCoord_Defs
public import Definitions.Def_ConjCoord_Reps
set_option autoImplicit true
@[expose] public section
public section
open Finset
open ConjCoord ConjCoord.Proof
variable {n : ℕ}

theorem ConjCoord.Proof.mem_sol111 {m : ℕ} (v : ℤ × ℤ × ℤ) :
    v ∈ sol 1 1 1 m ↔ v.1 ^ 2 + v.2.1 ^ 2 + v.2.2 ^ 2 = m := by sorry
