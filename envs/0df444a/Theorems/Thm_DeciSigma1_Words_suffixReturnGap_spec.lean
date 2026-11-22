-- Prove2me | Theorems.Thm_DeciSigma1_Words_suffixReturnGap_spec
-- name    : DeciSigma1.Words.suffixReturnGap_spec
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:48:48.227166+00:00
-- url     : https://prove2.me/theorems/d69f2bc2-382b-43f7-8968-53e61ca812b6
-- title:
--   Words: suffix Return Gap spec
-- statement:
--   The Words construction uses the suffix Return Gap spec property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Words/SuffixChains.lean#L93-L104
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Words/SuffixChains.lean#L93-L104

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

theorem DeciSigma1.Words.suffixReturnGap_spec {t : List α} {b h : ℕ} (hD : suffixReturnGap t b = some h) :
    b ≤ t.length ∧ 1 ≤ h ∧ b + h ≤ t.length ∧ suffixOfLength t b <:+ t.take (t.length - h) := by sorry
