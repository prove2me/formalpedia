-- Prove2me | Theorems.Thm_DeciSigma1_Words_SuffixChain_length_le_card
-- name    : DeciSigma1.Words.SuffixChain.length_le_card
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T13:07:52.278801+00:00
-- url     : https://prove2.me/theorems/ccdb63dc-e8e9-49f8-ba03-27430d780c94
-- title:
--   Suffix Chain: length le card
-- statement:
--   Counting chain members by an injective labeling that avoids one value.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Words/SuffixChains.lean#L260-L280
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Words/SuffixChains.lean#L260-L280

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

theorem DeciSigma1.Words.SuffixChain.length_le_card {S : Type} [Fintype S] {t : List α}
    {bs : List ℕ} (h : SuffixChain t bs) (f : ℕ → S) (d : S)
    (hinj : ∀ b ∈ bs, ∀ b' ∈ bs, b < b' → f b ≠ f b') (hd : ∀ b ∈ bs, f b ≠ d) :
    bs.length ≤ Fintype.card S - 1 := by sorry
