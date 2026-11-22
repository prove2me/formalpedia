-- Prove2me | Theorems.Thm_DeciSigma1_Words_deletePositions_snoc
-- name    : DeciSigma1.Words.deletePositions_snoc
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T13:03:08.267306+00:00
-- url     : https://prove2.me/theorems/c1721c91-4a54-4192-bff0-59ffddf8b67a
-- title:
--   Words: delete Positions snoc
-- statement:
--   The Words construction uses the delete Positions snoc property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Words/Deletion.lean#L166-L171
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Words/Deletion.lean#L166-L171

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

theorem DeciSigma1.Words.deletePositions_snoc (w : List α) (c : α) :
    deletePositions (w ++ [c]) D = deletePositions w D ++ if w.length ∈ D then [] else [c] := by sorry
