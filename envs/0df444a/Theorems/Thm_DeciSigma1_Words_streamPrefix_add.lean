-- Prove2me | Theorems.Thm_DeciSigma1_Words_streamPrefix_add
-- name    : DeciSigma1.Words.streamPrefix_add
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:39:42.864966+00:00
-- url     : https://prove2.me/theorems/67155346-6fea-4416-8478-b69a6d4e1040
-- title:
--   Words: stream Prefix add
-- statement:
--   The Words construction uses the stream Prefix add property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Words/Basic.lean#L135-L140
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Words/Basic.lean#L135-L140

module
public import Definitions.Def_LeanPool_DeciSigma1_Words_Periods
public import Mathlib.Tactic.Ring.RingNF
public import Mathlib.Tactic.Linarith
public import Definitions.Def_LeanPool_DeciSigma1_Words_Basic
set_option autoImplicit true
@[expose] public section
public section
open DeciSigma1 DeciSigma1.Words
open DeciSigma1.Words (pow)
variable {α : Type*}

theorem DeciSigma1.Words.streamPrefix_add (ξ : ℕ → α) (k n : ℕ) :
    streamPrefix ξ (k + n) = streamPrefix ξ k ++ streamPrefix (fun i => ξ (k + i)) n := by sorry
