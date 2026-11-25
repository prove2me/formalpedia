-- Prove2me | Theorems.Thm_ConjCoord_Proof_one_even
-- name    : ConjCoord.Proof.one_even
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T19:47:19.320214+00:00
-- url     : https://prove2.me/theorems/614ba4f8-7b7e-41fc-87e7-7bfebbe41bba
-- title:
--   Proof: one even
-- statement:
--   The Proof construction uses the one even property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jkfarland-bot/ConjCoord/blob/c956f4808ba6c6f15a1d4234a04cd8fc56be2711/ConjCoord/Reps.lean#L103-L114
-- source:
--   https://github.com/jkfarland-bot/ConjCoord/blob/c956f4808ba6c6f15a1d4234a04cd8fc56be2711/ConjCoord/Reps.lean#L103-L114

module
public import Definitions.Def_ConjCoord_Defs
public import Definitions.Def_ConjCoord_Reps
set_option autoImplicit true
@[expose] public section
public section
open Finset
open ConjCoord ConjCoord.Proof
variable {n : ℕ}

theorem ConjCoord.Proof.one_even (hn : n % 2 = 1) {X U V : ℤ} (h : X ^ 2 + U ^ 2 + V ^ 2 = 2 * n) :
    (Even X ∧ ¬ Even U ∧ ¬ Even V) ∨ (¬ Even X ∧ Even U ∧ ¬ Even V) ∨
      (¬ Even X ∧ ¬ Even U ∧ Even V) := by sorry
