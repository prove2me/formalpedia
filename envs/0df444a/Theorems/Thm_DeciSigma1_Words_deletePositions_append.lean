-- Prove2me | Theorems.Thm_DeciSigma1_Words_deletePositions_append
-- name    : DeciSigma1.Words.deletePositions_append
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:53:52.572799+00:00
-- url     : https://prove2.me/theorems/d026a205-8e17-426f-8bb2-c143eacc99ae
-- title:
--   Words: delete Positions append
-- statement:
--   The Words construction uses the delete Positions append property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Words/Deletion.lean#L160-L164
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Words/Deletion.lean#L160-L164

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

theorem DeciSigma1.Words.deletePositions_append (xs ys : List α) :
    deletePositions (xs ++ ys) D = deletePositions xs D ++
      ((ys.zipIdx xs.length).filter (fun p => p.2 ∉ D)).map Prod.fst := by sorry
