-- Prove2me | Theorems.Thm_DeciSigma1_Words_streamPrefix_suffix_iff
-- name    : DeciSigma1.Words.streamPrefix_suffix_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:39:41.418112+00:00
-- url     : https://prove2.me/theorems/58e9047a-315c-4843-8971-9174373df668
-- title:
--   Words: stream Prefix suffix iff
-- statement:
--   The Words construction uses the stream Prefix suffix iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Words/Basic.lean#L301-L322
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Words/Basic.lean#L301-L322

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

theorem DeciSigma1.Words.streamPrefix_suffix_iff (ξ η : ℕ → α) (m n : ℕ) :
    streamPrefix η m <:+ streamPrefix ξ n ↔ m ≤ n ∧ ∀ t < m, η t = ξ (n - m + t) := by sorry
