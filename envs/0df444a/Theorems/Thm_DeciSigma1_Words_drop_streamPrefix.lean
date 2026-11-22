-- Prove2me | Theorems.Thm_DeciSigma1_Words_drop_streamPrefix
-- name    : DeciSigma1.Words.drop_streamPrefix
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:39:51.039818+00:00
-- url     : https://prove2.me/theorems/013264a9-62d9-4589-9e40-a9adc795d609
-- title:
--   Words: drop stream Prefix
-- statement:
--   The Words construction uses the drop stream Prefix property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Words/Basic.lean#L270-L273
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Words/Basic.lean#L270-L273

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

theorem DeciSigma1.Words.drop_streamPrefix (ξ : ℕ → α) {a n : ℕ} (ha : a ≤ n) :
    (streamPrefix ξ n).drop a = streamPrefix (fun t => ξ (a + t)) (n - a) := by sorry
