-- Prove2me | Theorems.Thm_DeciSigma1_Words_retainedCount_le
-- name    : DeciSigma1.Words.retainedCount_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:50:18.009794+00:00
-- url     : https://prove2.me/theorems/e6e59aea-c63e-41b9-b9ae-eae49668b58c
-- title:
--   Words: retained Count le
-- statement:
--   The Words construction uses the retained Count le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Words/Deletion.lean#L121-L122
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Words/Deletion.lean#L121-L122

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

theorem DeciSigma1.Words.retainedCount_le (a : ℕ) : retainedCount D a ≤ a := by sorry
