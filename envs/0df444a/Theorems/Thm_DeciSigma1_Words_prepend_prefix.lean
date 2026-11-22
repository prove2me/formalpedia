-- Prove2me | Theorems.Thm_DeciSigma1_Words_prepend_prefix
-- name    : DeciSigma1.Words.prepend_prefix
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:58:37.636432+00:00
-- url     : https://prove2.me/theorems/f1a3a700-50d0-4abd-9ab8-b8965961c9bb
-- title:
--   Words: prepend prefix
-- statement:
--   The Words construction uses the prepend prefix property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Words/Basic.lean#L85-L87
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Words/Basic.lean#L85-L87

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

theorem DeciSigma1.Words.prepend_prefix (w : List α) (ξ : ℕ → α) :
    streamPrefix (prepend w ξ) w.length = w := by sorry
