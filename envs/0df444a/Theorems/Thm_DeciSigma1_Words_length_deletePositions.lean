-- Prove2me | Theorems.Thm_DeciSigma1_Words_length_deletePositions
-- name    : DeciSigma1.Words.length_deletePositions
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:42:48.197281+00:00
-- url     : https://prove2.me/theorems/d6a39b88-aafb-4386-bf8f-a3abc7ad0c13
-- title:
--   Words: length delete Positions
-- statement:
--   The Words construction uses the length delete Positions property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Words/Deletion.lean#L194-L197
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Words/Deletion.lean#L194-L197

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

theorem DeciSigma1.Words.length_deletePositions (w : List α) :
    (deletePositions w D).length = retainedCount D w.length := by sorry
