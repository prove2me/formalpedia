-- Prove2me | Theorems.Thm_DeciSigma1_Words_deletePositions_take_succ
-- name    : DeciSigma1.Words.deletePositions_take_succ
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:48:29.32885+00:00
-- url     : https://prove2.me/theorems/a52312fe-795a-48cc-ad30-b6e6b2d57834
-- title:
--   Words: delete Positions take succ
-- statement:
--   The Words construction uses the delete Positions take succ property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Words/Deletion.lean#L175-L183
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Words/Deletion.lean#L175-L183

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

theorem DeciSigma1.Words.deletePositions_take_succ (w : List α) (c : ℕ) :
    deletePositions (w.take (c + 1)) D = deletePositions (w.take c) D ++ if c ∈
        D then [] else (w[c]?).toList := by sorry
