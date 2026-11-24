-- Prove2me | Theorems.Thm_BalanceSpecification_MarkerEmbedding_wordFinset_renamedShift
-- name    : BalanceSpecification.MarkerEmbedding.wordFinset_renamedShift
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T01:56:12.069641+00:00
-- url     : https://prove2.me/theorems/ab4c95ed-b17c-4b6e-a6ac-c520fe39c5a2
-- title:
--   Marker Embedding: word Finset renamed Shift
-- statement:
--   The Marker Embedding construction uses the word Finset renamed Shift property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/pseudorandom/balance_and_specification/blob/62771ced95e6f431064d40780b623362263ae9e4/BalanceSpecificaton/MarkerEmbedding.lean#L79-L89
-- source:
--   https://github.com/pseudorandom/balance_and_specification/blob/62771ced95e6f431064d40780b623362263ae9e4/BalanceSpecificaton/MarkerEmbedding.lean#L79-L89

module
public import Definitions.Def_BalanceSpecificaton_Entropy
public import Definitions.Def_BalanceSpecificaton_Specification
public import Definitions.Def_BalanceSpecificaton_LanguageProperties
public import Mathlib.Tactic
public import Definitions.Def_BalanceSpecificaton_MarkerEmbedding
set_option autoImplicit true
@[expose] public section
public section
noncomputable section
open BalanceSpecification BalanceSpecification.MarkerEmbedding
variable {A B : Type*}
variable [TopologicalSpace A] [DiscreteTopology A] [Fintype A]
  [TopologicalSpace B] [T2Space B]
open scoped Classical

theorem BalanceSpecification.MarkerEmbedding.wordFinset_renamedShift [Fintype B] (f : A → B) (Y : ShiftSpace A) (n : ℕ) :
    wordFinset (language (renamedShift f Y)) n =
      (wordFinset (language Y) n).image (List.map f) := by sorry
