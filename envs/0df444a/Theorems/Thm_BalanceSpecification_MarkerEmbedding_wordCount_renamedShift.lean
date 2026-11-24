-- Prove2me | Theorems.Thm_BalanceSpecification_MarkerEmbedding_wordCount_renamedShift
-- name    : BalanceSpecification.MarkerEmbedding.wordCount_renamedShift
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T01:56:02.19449+00:00
-- url     : https://prove2.me/theorems/04cf6e1d-de97-4197-ac9c-efbcef87a575
-- title:
--   Marker Embedding: word Count renamed Shift
-- statement:
--   Injective renaming preserves every finite block count exactly.
--
--   Source: https://github.com/pseudorandom/balance_and_specification/blob/62771ced95e6f431064d40780b623362263ae9e4/BalanceSpecificaton/MarkerEmbedding.lean#L92-L100
-- source:
--   https://github.com/pseudorandom/balance_and_specification/blob/62771ced95e6f431064d40780b623362263ae9e4/BalanceSpecificaton/MarkerEmbedding.lean#L92-L100

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

theorem BalanceSpecification.MarkerEmbedding.wordCount_renamedShift [Fintype B] {f : A → B} (hf : Function.Injective f)
    (Y : ShiftSpace A) (n : ℕ) :
    wordCount (language (renamedShift f Y)) n = wordCount (language Y) n := by sorry
