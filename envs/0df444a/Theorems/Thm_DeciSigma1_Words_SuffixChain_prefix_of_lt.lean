-- Prove2me | Theorems.Thm_DeciSigma1_Words_SuffixChain_prefix_of_lt
-- name    : DeciSigma1.Words.SuffixChain.prefix_of_lt
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:56:21.106644+00:00
-- url     : https://prove2.me/theorems/1a11e5c5-6643-4611-9ad8-936243ab6d24
-- title:
--   Suffix Chain: prefix of lt
-- statement:
--   Two members `b < b'` of a suffix chain have `v_b` a prefix of `v_{b'}`.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Words/SuffixChains.lean#L247-L257
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Words/SuffixChains.lean#L247-L257

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

theorem DeciSigma1.Words.SuffixChain.prefix_of_lt {t : List α} {bs : List ℕ}
    (h : SuffixChain t bs)
    {b b' : ℕ} (hb : b ∈ bs) (hb' : b' ∈ bs) (hlt : b < b') : suffixOfLength t b <+:
        suffixOfLength t b' := by sorry
