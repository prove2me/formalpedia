-- Prove2me | Theorems.Thm_DeciSigma1_Words_suffixOfLength_suffix_suffixOfLength
-- name    : DeciSigma1.Words.suffixOfLength_suffix_suffixOfLength
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:56:08.044805+00:00
-- url     : https://prove2.me/theorems/ca9b8bb4-417a-4f57-9573-8cfedc22b173
-- title:
--   Words: suffix Of Length suffix suffix Of Length
-- statement:
--   The Words construction uses the suffix Of Length suffix suffix Of Length property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Words/SuffixChains.lean#L57-L64
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Words/SuffixChains.lean#L57-L64

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

theorem DeciSigma1.Words.suffixOfLength_suffix_suffixOfLength (t : List α) {b b' : ℕ} (h : b ≤ b') :
    suffixOfLength t b <:+ suffixOfLength t b' := by sorry
