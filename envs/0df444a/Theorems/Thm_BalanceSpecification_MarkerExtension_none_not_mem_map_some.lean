-- Prove2me | Theorems.Thm_BalanceSpecification_MarkerExtension_none_not_mem_map_some
-- name    : BalanceSpecification.MarkerExtension.none_not_mem_map_some
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T01:59:47.150214+00:00
-- url     : https://prove2.me/theorems/c70cb805-e1e8-4bfe-a2ed-f72f2a08411b
-- title:
--   Marker Extension: none not mem map some
-- statement:
--   The Marker Extension construction uses the none not mem map some property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/pseudorandom/balance_and_specification/blob/62771ced95e6f431064d40780b623362263ae9e4/BalanceSpecificaton/MarkerExtension.lean#L23-L26
-- source:
--   https://github.com/pseudorandom/balance_and_specification/blob/62771ced95e6f431064d40780b623362263ae9e4/BalanceSpecificaton/MarkerExtension.lean#L23-L26

module
public import Definitions.Def_BalanceSpecificaton_MarkerEmbedding
public import Definitions.Def_BalanceSpecificaton_CodedLanguage
public import Definitions.Def_BalanceSpecificaton_Synchronization
public import Mathlib.Tactic
public import Definitions.Def_BalanceSpecificaton_MarkerExtension
set_option autoImplicit true
@[expose] public section
public section
noncomputable section
open BalanceSpecification BalanceSpecification.MarkerExtension
variable {A : Type*}

theorem BalanceSpecification.MarkerExtension.none_not_mem_map_some (v : Word A) : (none : Option A) ∉ v.map some := by sorry
