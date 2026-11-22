-- Prove2me | Theorems.Thm_DeciSigma1_Words_two_le_card_of_eligible
-- name    : DeciSigma1.Words.two_le_card_of_eligible
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T13:08:00.695992+00:00
-- url     : https://prove2.me/theorems/7c4cca7d-d951-4d59-bd67-b6c976f32b6e
-- title:
--   Words: two le card of eligible
-- statement:
--   The Words construction uses the two le card of eligible property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Words/SuffixChains.lean#L290-L296
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Words/SuffixChains.lean#L290-L296

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
variable {S : Type} [Fintype S] {k : ℕ} (M : StructuralReader α S k)
  {W : Fin k → List α} {j : Fin k}
omit [DecidableEq α]

theorem DeciSigma1.Words.two_le_card_of_eligible (h : M.Eligible W j) : 2 ≤ Fintype.card S := by sorry
