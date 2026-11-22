-- Prove2me | Theorems.Thm_DeciSigma1_Words_deletePositions_empty
-- name    : DeciSigma1.Words.deletePositions_empty
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:42:07.482101+00:00
-- url     : https://prove2.me/theorems/57c55b82-5a71-4dc0-8c33-a9fbd9af2852
-- title:
--   Words: delete Positions empty
-- statement:
--   The Words construction uses the delete Positions empty property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Words/Deletion.lean#L284-L287
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Words/Deletion.lean#L284-L287

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

theorem DeciSigma1.Words.deletePositions_empty (w : List α) : deletePositions w ∅ = w := by sorry
