-- Prove2me | Theorems.Thm_DeciSigma1_Words_deletePositions_take
-- name    : DeciSigma1.Words.deletePositions_take
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:50:18.243803+00:00
-- url     : https://prove2.me/theorems/a08e8007-1411-4b96-8041-371bf54ff7a7
-- title:
--   Words: delete Positions take
-- statement:
--   The Words construction uses the delete Positions take property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Words/Deletion.lean#L199-L202
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Words/Deletion.lean#L199-L202

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

theorem DeciSigma1.Words.deletePositions_take (w : List α) {a : ℕ} (ha : a ≤ w.length) :
    (deletePositions w D).take (retainedCount D a) = deletePositions (w.take a) D := by sorry
