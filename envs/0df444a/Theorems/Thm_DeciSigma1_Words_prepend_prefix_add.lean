-- Prove2me | Theorems.Thm_DeciSigma1_Words_prepend_prefix_add
-- name    : DeciSigma1.Words.prepend_prefix_add
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:58:37.832813+00:00
-- url     : https://prove2.me/theorems/00ccf496-f729-4b2c-95ed-a91707dda8c4
-- title:
--   Words: prepend prefix add
-- statement:
--   The Words construction uses the prepend prefix add property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Words/Basic.lean#L89-L96
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Words/Basic.lean#L89-L96

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

theorem DeciSigma1.Words.prepend_prefix_add (w : List α) (ξ : ℕ → α) (n : ℕ) :
    streamPrefix (prepend w ξ) (w.length + n) = w ++ streamPrefix ξ n := by sorry
