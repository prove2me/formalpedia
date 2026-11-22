-- Prove2me | Theorems.Thm_DeciSigma1_Words_SuffixChain_nodup
-- name    : DeciSigma1.Words.SuffixChain.nodup
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:51:38.419999+00:00
-- url     : https://prove2.me/theorems/bf35c501-4fbe-4501-8816-3ab346242e07
-- title:
--   Suffix Chain: nodup
-- statement:
--   The Suffix Chain construction uses the nodup property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Words/SuffixChains.lean#L195-L196
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Words/SuffixChains.lean#L195-L196

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

theorem DeciSigma1.Words.SuffixChain.nodup {t : List α} {bs : List ℕ} (h : SuffixChain t bs) : bs.Nodup := by sorry
