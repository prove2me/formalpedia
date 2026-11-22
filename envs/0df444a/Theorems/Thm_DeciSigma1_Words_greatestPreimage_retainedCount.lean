-- Prove2me | Theorems.Thm_DeciSigma1_Words_greatestPreimage_retainedCount
-- name    : DeciSigma1.Words.greatestPreimage_retainedCount
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:45:35.425303+00:00
-- url     : https://prove2.me/theorems/57c57f02-bea8-4256-8fa2-1684f6658730
-- title:
--   Words: greatest Preimage retained Count
-- statement:
--   The Words construction uses the greatest Preimage retained Count property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Words/Deletion.lean#L261-L266
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Words/Deletion.lean#L261-L266

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

theorem DeciSigma1.Words.greatestPreimage_retainedCount {p : ℕ} (h : p ∉ D) :
    greatestPreimage D (retainedCount D p) = p := by sorry
