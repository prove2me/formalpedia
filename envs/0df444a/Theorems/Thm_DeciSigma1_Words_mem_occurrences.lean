-- Prove2me | Theorems.Thm_DeciSigma1_Words_mem_occurrences
-- name    : DeciSigma1.Words.mem_occurrences
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:46:31.851594+00:00
-- url     : https://prove2.me/theorems/667f9ae5-6639-4581-84e0-b1b0aa48cc03
-- title:
--   Words: mem occurrences
-- statement:
--   The Words construction uses the mem occurrences property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Words/SuffixChains.lean#L73-L75
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Words/SuffixChains.lean#L73-L75

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

theorem DeciSigma1.Words.mem_occurrences {x t : List α} {b e : ℕ} :
    e ∈ occurrences x t b ↔ e ≤ x.length ∧ b ≤ t.length ∧ suffixOfLength t b <:+ x.take e := by sorry
