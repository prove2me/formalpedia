-- Prove2me | Theorems.Thm_DeciSigma1_Words_suffixReturnGap_mono
-- name    : DeciSigma1.Words.suffixReturnGap_mono
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T13:07:35.862239+00:00
-- url     : https://prove2.me/theorems/fdd45d86-84b1-4b6e-ae13-a99f2d06289e
-- title:
--   Words: suffix Return Gap mono
-- statement:
--   `suffixReturnGap t` is monotone: an occurrence of a longer suffix contains an occurrence of the
--   shorter suffix at the same distance from the end.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Words/SuffixChains.lean#L133-L138
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Words/SuffixChains.lean#L133-L138

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

theorem DeciSigma1.Words.suffixReturnGap_mono {t : List α} {b b' h' : ℕ} (hbb : b ≤ b')
    (hD : suffixReturnGap t b' = some h') :
    ∃ h, suffixReturnGap t b = some h ∧ h ≤ h' := by sorry
