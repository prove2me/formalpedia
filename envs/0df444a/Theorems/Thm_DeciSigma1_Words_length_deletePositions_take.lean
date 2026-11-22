-- Prove2me | Theorems.Thm_DeciSigma1_Words_length_deletePositions_take
-- name    : DeciSigma1.Words.length_deletePositions_take
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T13:03:10.571796+00:00
-- url     : https://prove2.me/theorems/9fe38c30-3b47-445b-a411-ad71a1ffb214
-- title:
--   Words: length delete Positions take
-- statement:
--   The Words construction uses the length delete Positions take property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Words/Deletion.lean#L185-L192
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Words/Deletion.lean#L185-L192

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

theorem DeciSigma1.Words.length_deletePositions_take (w : List α) {c : ℕ} (hc : c ≤ w.length) :
    (deletePositions (w.take c) D).length = retainedCount D c := by sorry
