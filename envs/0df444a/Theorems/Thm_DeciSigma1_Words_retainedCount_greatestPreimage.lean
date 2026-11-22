-- Prove2me | Theorems.Thm_DeciSigma1_Words_retainedCount_greatestPreimage
-- name    : DeciSigma1.Words.retainedCount_greatestPreimage
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:42:04.348477+00:00
-- url     : https://prove2.me/theorems/c1804054-ebb1-410f-97aa-717604953c06
-- title:
--   Words: retained Count greatest Preimage
-- statement:
--   The Words construction uses the retained Count greatest Preimage property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Words/Deletion.lean#L246-L252
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Words/Deletion.lean#L246-L252

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

theorem DeciSigma1.Words.retainedCount_greatestPreimage (a : ℕ) :
    retainedCount D (greatestPreimage D a) = a := by sorry
