-- Prove2me | Theorems.Thm_DeciSigma1_Words_retainedCount_succ
-- name    : DeciSigma1.Words.retainedCount_succ
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:46:49.78125+00:00
-- url     : https://prove2.me/theorems/d9617ad1-7634-45d2-bef0-2a8a6788770b
-- title:
--   Words: retained Count succ
-- statement:
--   The Words construction uses the retained Count succ property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Words/Deletion.lean#L71-L77
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Words/Deletion.lean#L71-L77

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

theorem DeciSigma1.Words.retainedCount_succ (a : ℕ) :
    retainedCount D (a + 1) = retainedCount D a + if a ∈ D then 0 else 1 := by sorry
