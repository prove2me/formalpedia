-- Prove2me | Theorems.Thm_DeciSigma1_Words_ChainBound_mono
-- name    : DeciSigma1.Words.ChainBound.mono
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:42:39.95582+00:00
-- url     : https://prove2.me/theorems/e7cfd1a3-8fb8-4e98-859f-625e74091d7b
-- title:
--   Chain Bound: mono
-- statement:
--   The Chain Bound construction uses the mono property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Words/SuffixChains.lean#L227-L230
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Words/SuffixChains.lean#L227-L230

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

theorem DeciSigma1.Words.ChainBound.mono {t : List α} {Sb Sb' : ℕ}
    (h : ChainBound t Sb)
    (hS : Sb ≤ Sb') : ChainBound t Sb' := by sorry
