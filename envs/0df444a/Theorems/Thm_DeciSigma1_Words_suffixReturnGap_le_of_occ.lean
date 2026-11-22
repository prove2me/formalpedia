-- Prove2me | Theorems.Thm_DeciSigma1_Words_suffixReturnGap_le_of_occ
-- name    : DeciSigma1.Words.suffixReturnGap_le_of_occ
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:51:34.663235+00:00
-- url     : https://prove2.me/theorems/1580494c-0f10-4fa8-9122-f1420375489f
-- title:
--   Words: suffix Return Gap le of occ
-- statement:
--   An occurrence of `v_b` ending `h` letters before the end bounds `suffixReturnGap t b` by
--   `h`.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Words/SuffixChains.lean#L108-L129
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Words/SuffixChains.lean#L108-L129

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

theorem DeciSigma1.Words.suffixReturnGap_le_of_occ {t : List α} {b h : ℕ} (hb : b ≤ t.length) (h1 : 1 ≤ h)
    (h2 : h ≤ t.length)
    (hocc : suffixOfLength t b <:+ t.take (t.length - h)) : ∃ h₀, suffixReturnGap t b = some h₀ ∧
        h₀ ≤
        h := by sorry
