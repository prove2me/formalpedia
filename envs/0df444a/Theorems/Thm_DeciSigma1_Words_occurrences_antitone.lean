-- Prove2me | Theorems.Thm_DeciSigma1_Words_occurrences_antitone
-- name    : DeciSigma1.Words.occurrences_antitone
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:56:06.68116+00:00
-- url     : https://prove2.me/theorems/eb8d3c0f-3612-4872-be29-c121a0dd21bb
-- title:
--   Words: occurrences antitone
-- statement:
--   The Words construction uses the occurrences antitone property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Words/SuffixChains.lean#L77-L81
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Words/SuffixChains.lean#L77-L81

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

theorem DeciSigma1.Words.occurrences_antitone {x t : List α} {b b' : ℕ} (h : b ≤ b') :
    occurrences x t b' ⊆ occurrences x t b := by sorry
