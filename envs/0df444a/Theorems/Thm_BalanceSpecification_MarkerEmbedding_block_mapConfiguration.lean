-- Prove2me | Theorems.Thm_BalanceSpecification_MarkerEmbedding_block_mapConfiguration
-- name    : BalanceSpecification.MarkerEmbedding.block_mapConfiguration
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T01:32:49.357803+00:00
-- url     : https://prove2.me/theorems/587d8a99-91ff-488c-9753-40ec7231a0b4
-- title:
--   Marker Embedding: block map Configuration
-- statement:
--   The Marker Embedding construction uses the block map Configuration property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/pseudorandom/balance_and_specification/blob/62771ced95e6f431064d40780b623362263ae9e4/BalanceSpecificaton/MarkerEmbedding.lean#L23-L27
-- source:
--   https://github.com/pseudorandom/balance_and_specification/blob/62771ced95e6f431064d40780b623362263ae9e4/BalanceSpecificaton/MarkerEmbedding.lean#L23-L27

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

theorem BalanceSpecification.MarkerEmbedding.block_mapConfiguration (f : A → B) (x : Configuration A)
    (k : ℤ) (n : ℕ) :
    block (mapConfiguration f x) k n = (block x k n).map f := by sorry
