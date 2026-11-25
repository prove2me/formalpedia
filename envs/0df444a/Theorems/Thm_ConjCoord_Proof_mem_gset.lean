-- Prove2me | Theorems.Thm_ConjCoord_Proof_mem_gset
-- name    : ConjCoord.Proof.mem_gset
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T19:50:08.201491+00:00
-- url     : https://prove2.me/theorems/68487bd4-865c-4611-9339-5583c52d1fa9
-- title:
--   Proof: mem gset
-- statement:
--   The Proof construction uses the mem gset property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jkfarland-bot/ConjCoord/blob/c956f4808ba6c6f15a1d4234a04cd8fc56be2711/ConjCoord/TwoSquares.lean#L95-L105
-- source:
--   https://github.com/jkfarland-bot/ConjCoord/blob/c956f4808ba6c6f15a1d4234a04cd8fc56be2711/ConjCoord/TwoSquares.lean#L95-L105

module
public import Definitions.Def_ConjCoord_Reps
public import Definitions.Def_ConjCoord_TwoSquares
set_option autoImplicit true
@[expose] public section
public section
open Finset
open ConjCoord ConjCoord.Proof

theorem ConjCoord.Proof.mem_gset {m : ℕ} (v : ℤ × ℤ × ℤ) :
    v ∈ gset m ↔ v.1 ^ 2 + v.2.1 ^ 2 + 16 * v.2.2 ^ 2 = (m : ℤ) ∧
      (v.1 ^ 2 + v.2.1 ^ 2) % 16 = 5 ∧ (v.2.1 % 16 = 6 ∨ v.2.1 % 16 = 10) := by sorry
