-- Prove2me | Theorems.Thm_DeciSigma1_Words_streamPrefix_succ
-- name    : DeciSigma1.Words.streamPrefix_succ
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:39:41.648851+00:00
-- url     : https://prove2.me/theorems/fb8b8a64-9201-48e1-9b25-9e941923e972
-- title:
--   Words: stream Prefix succ
-- statement:
--   The Words construction uses the stream Prefix succ property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Words/Basic.lean#L63-L66
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Words/Basic.lean#L63-L66

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

theorem DeciSigma1.Words.streamPrefix_succ (ξ : ℕ → α) (n : ℕ) :
    streamPrefix ξ (n + 1) = streamPrefix ξ n ++ [ξ n] := by sorry
