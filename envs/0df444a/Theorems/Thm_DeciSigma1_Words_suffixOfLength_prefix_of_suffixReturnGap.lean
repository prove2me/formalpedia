-- Prove2me | Theorems.Thm_DeciSigma1_Words_suffixOfLength_prefix_of_suffixReturnGap
-- name    : DeciSigma1.Words.suffixOfLength_prefix_of_suffixReturnGap
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T13:07:41.857599+00:00
-- url     : https://prove2.me/theorems/269037c5-11c6-4d40-83dc-819a9fed9b22
-- title:
--   Words: suffix Of Length prefix of suffix Return Gap
-- statement:
--   One chain step makes `v_b` a prefix of `v_{b+h}`.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Words/SuffixChains.lean#L141-L155
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Words/SuffixChains.lean#L141-L155

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

theorem DeciSigma1.Words.suffixOfLength_prefix_of_suffixReturnGap {t : List α} {b h : ℕ}
    (hD : suffixReturnGap t b = some h) :
    suffixOfLength t b <+: suffixOfLength t (b + h) := by sorry
