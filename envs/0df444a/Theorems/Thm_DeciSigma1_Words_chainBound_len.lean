-- Prove2me | Theorems.Thm_DeciSigma1_Words_chainBound_len
-- name    : DeciSigma1.Words.chainBound_len
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T13:07:49.880883+00:00
-- url     : https://prove2.me/theorems/289c1669-d8e8-41d8-8f5b-79421a537b6f
-- title:
--   Words: chain Bound len
-- statement:
--   Every chain has at most `|t| + 1` members.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Words/SuffixChains.lean#L211-L225
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Words/SuffixChains.lean#L211-L225

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
variable [DecidableEq α]

theorem DeciSigma1.Words.chainBound_len (t : List α) : ChainBound t t.length := by sorry
