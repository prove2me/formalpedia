-- Prove2me | Theorems.Thm_DeciSigma1_Words_length_suffixOfLength
-- name    : DeciSigma1.Words.length_suffixOfLength
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:42:16.30578+00:00
-- url     : https://prove2.me/theorems/4a7b231e-d923-4d71-92e6-2fb8509d212f
-- title:
--   Words: length suffix Of Length
-- statement:
--   The Words construction uses the length suffix Of Length property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Words/SuffixChains.lean#L53-L55
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Words/SuffixChains.lean#L53-L55

module
public import Definitions.Def_LeanPool_DeciSigma1_Readers_Basic
public import Mathlib.Order.Interval.Finset.Nat
public import Definitions.Def_LeanPool_DeciSigma1_Words_SuffixChains
set_option autoImplicit true
@[expose] public section
public section
open DeciSigma1 DeciSigma1.Words
open DeciSigma1.Readers
variable {α : Type}

theorem DeciSigma1.Words.length_suffixOfLength (t : List α) (b : ℕ) :
    (suffixOfLength t b).length = min b t.length := by sorry
