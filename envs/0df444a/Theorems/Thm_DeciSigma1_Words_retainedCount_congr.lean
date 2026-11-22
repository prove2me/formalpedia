-- Prove2me | Theorems.Thm_DeciSigma1_Words_retainedCount_congr
-- name    : DeciSigma1.Words.retainedCount_congr
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T13:03:00.389805+00:00
-- url     : https://prove2.me/theorems/9d6cf387-786b-4414-bcd5-c1eab909c14a
-- title:
--   Words: retained Count congr
-- statement:
--   The Words construction uses the retained Count congr property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Words/Deletion.lean#L131-L135
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Words/Deletion.lean#L131-L135

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

theorem DeciSigma1.Words.retainedCount_congr {D' : Finset ℕ} {a : ℕ} (h : ∀ p < a, p ∈ D ↔ p ∈ D') :
    retainedCount D a = retainedCount D' a := by sorry
