-- Prove2me | Theorems.Thm_DeciSigma1_Words_SuffixChain_le_length
-- name    : DeciSigma1.Words.SuffixChain.le_length
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:51:45.079228+00:00
-- url     : https://prove2.me/theorems/0a4c1f85-fb3f-4e91-a434-1978b5d22808
-- title:
--   Suffix Chain: le length
-- statement:
--   In a chain with at least two members every member is `≤ |t|`.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Words/SuffixChains.lean#L199-L208
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Words/SuffixChains.lean#L199-L208

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

theorem DeciSigma1.Words.SuffixChain.le_length {t : List α} {bs : List ℕ} (h : SuffixChain t bs)
    (h2 : 2 ≤ bs.length) :
    ∀ b ∈ bs, b ≤ t.length := by sorry
