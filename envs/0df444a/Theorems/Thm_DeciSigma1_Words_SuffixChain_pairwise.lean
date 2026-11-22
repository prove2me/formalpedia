-- Prove2me | Theorems.Thm_DeciSigma1_Words_SuffixChain_pairwise
-- name    : DeciSigma1.Words.SuffixChain.pairwise
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:46:39.173858+00:00
-- url     : https://prove2.me/theorems/156ef624-66d3-48f7-b599-9c8fe7e2d758
-- title:
--   Suffix Chain: pairwise
-- statement:
--   The members of a chain increase, all but the first are at most `|t|`, and their suffixes
--   form a prefix chain.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Words/SuffixChains.lean#L178-L193
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Words/SuffixChains.lean#L178-L193

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

theorem DeciSigma1.Words.SuffixChain.pairwise {t : List α} {bs : List ℕ} (h : SuffixChain t bs) :
    bs.Pairwise
        (fun b b' => b < b' ∧ b' ≤ t.length ∧ suffixOfLength t b <+: suffixOfLength t b') := by sorry
