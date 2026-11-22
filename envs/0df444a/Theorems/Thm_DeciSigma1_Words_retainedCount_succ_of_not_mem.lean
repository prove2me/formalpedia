-- Prove2me | Theorems.Thm_DeciSigma1_Words_retainedCount_succ_of_not_mem
-- name    : DeciSigma1.Words.retainedCount_succ_of_not_mem
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:46:18.61161+00:00
-- url     : https://prove2.me/theorems/b01a3f50-c2b4-4ab4-bff5-6f032f992a86
-- title:
--   Words: retained Count succ of not mem
-- statement:
--   The Words construction uses the retained Count succ of not mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Words/Deletion.lean#L79-L81
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Words/Deletion.lean#L79-L81

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

theorem DeciSigma1.Words.retainedCount_succ_of_not_mem {a : ℕ} (h : a ∉ D) :
    retainedCount D (a + 1) = retainedCount D a + 1 := by sorry
