-- Prove2me | Theorems.Thm_DeciSigma1_Words_greatestPreimage_lt_length
-- name    : DeciSigma1.Words.greatestPreimage_lt_length
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T13:03:19.276382+00:00
-- url     : https://prove2.me/theorems/6f56d985-2700-4471-b411-9f98bbc8787d
-- title:
--   Words: greatest Preimage lt length
-- statement:
--   The Words construction uses the greatest Preimage lt length property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Words/Deletion.lean#L289-L294
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Words/Deletion.lean#L289-L294

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

theorem DeciSigma1.Words.greatestPreimage_lt_length (w : List α) {a : ℕ} (ha : a < (deletePositions w D).length) :
    greatestPreimage D a < w.length := by sorry
