-- Prove2me | Theorems.Thm_DeciSigma1_Words_deletePositions_union_Ico
-- name    : DeciSigma1.Words.deletePositions_union_Ico
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T13:03:28.398511+00:00
-- url     : https://prove2.me/theorems/78002cb2-96f6-49aa-985f-3e3c6354862a
-- title:
--   Words: delete Positions union Ico
-- statement:
--   The Words construction uses the delete Positions union Ico property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Words/Deletion.lean#L486-L497
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Words/Deletion.lean#L486-L497

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
variable {c δ : ℕ}

theorem DeciSigma1.Words.deletePositions_union_Ico (w : List α) (hD : ∀ p ∈ D, p < c) (hc : c ≤ w.length) :
    deletePositions w (D ∪ Finset.Ico c (c + δ)) =
      deletePositions (w.take c ++ w.drop (c + δ)) D := by sorry
