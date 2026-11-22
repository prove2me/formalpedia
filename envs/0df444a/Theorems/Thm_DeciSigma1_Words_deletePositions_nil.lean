-- Prove2me | Theorems.Thm_DeciSigma1_Words_deletePositions_nil
-- name    : DeciSigma1.Words.deletePositions_nil
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:42:07.004841+00:00
-- url     : https://prove2.me/theorems/3b35d947-be00-4b88-8cfc-66166c6ffba9
-- title:
--   Words: delete Positions nil
-- statement:
--   The Words construction uses the delete Positions nil property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Words/Deletion.lean#L173-L173
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Words/Deletion.lean#L173-L173

module
public import Definitions.Def_LeanPool_DeciSigma1_Readers_Basic
public import Mathlib.Tactic.Ring.RingNF
public import Mathlib.Order.Interval.Finset.Nat
public import Definitions.Def_LeanPool_DeciSigma1_Words_Deletion
set_option autoImplicit true
@[expose] public section
public section
open DeciSigma1 DeciSigma1.Words
open DeciSigma1.Readers
variable {α S : Type} {k : ℕ}
variable {D : Finset ℕ}

theorem DeciSigma1.Words.deletePositions_nil : deletePositions ([] : List α) D = [] := by sorry

attribute [defeq] DeciSigma1.Words.deletePositions_nil
