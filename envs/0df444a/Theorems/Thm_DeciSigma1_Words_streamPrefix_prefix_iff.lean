-- Prove2me | Theorems.Thm_DeciSigma1_Words_streamPrefix_prefix_iff
-- name    : DeciSigma1.Words.streamPrefix_prefix_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:58:40.812437+00:00
-- url     : https://prove2.me/theorems/3e68cf34-2d0f-44e7-b907-3dba9fe92bd5
-- title:
--   Words: stream Prefix prefix iff
-- statement:
--   The Words construction uses the stream Prefix prefix iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Words/Basic.lean#L275-L289
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Words/Basic.lean#L275-L289

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
variable {α : Type}

theorem DeciSigma1.Words.streamPrefix_prefix_iff (ξ η : ℕ → α) (m m' : ℕ) :
    streamPrefix η m <+: streamPrefix ξ m' ↔ m ≤ m' ∧ ∀ t < m, η t = ξ t := by sorry
