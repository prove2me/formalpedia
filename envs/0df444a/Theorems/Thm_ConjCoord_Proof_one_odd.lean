-- Prove2me | Theorems.Thm_ConjCoord_Proof_one_odd
-- name    : ConjCoord.Proof.one_odd
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T19:47:05.973698+00:00
-- url     : https://prove2.me/theorems/045ce1ea-df34-430e-90f1-d3b048d18948
-- title:
--   Proof: one odd
-- statement:
--   The Proof construction uses the one odd property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jkfarland-bot/ConjCoord/blob/c956f4808ba6c6f15a1d4234a04cd8fc56be2711/ConjCoord/Reps.lean#L90-L101
-- source:
--   https://github.com/jkfarland-bot/ConjCoord/blob/c956f4808ba6c6f15a1d4234a04cd8fc56be2711/ConjCoord/Reps.lean#L90-L101

module
public import Definitions.Def_ConjCoord_Defs
public import Definitions.Def_ConjCoord_Reps
set_option autoImplicit true
@[expose] public section
public section
open Finset
open ConjCoord ConjCoord.Proof
variable {n : ℕ}

theorem ConjCoord.Proof.one_odd (hn : n % 4 = 1) {X U V : ℤ} (h : X ^ 2 + U ^ 2 + V ^ 2 = n) :
    (Odd X ∧ ¬ Odd U ∧ ¬ Odd V) ∨ (¬ Odd X ∧ Odd U ∧ ¬ Odd V) ∨
      (¬ Odd X ∧ ¬ Odd U ∧ Odd V) := by sorry
