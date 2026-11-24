-- Prove2me | Theorems.Thm_BalanceSpecification_MarkerExtension_exists_map_some_of_markerFree
-- name    : BalanceSpecification.MarkerExtension.exists_map_some_of_markerFree
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-24T02:01:30.018213+00:00
-- url     : https://prove2.me/theorems/a21cc288-8590-4a26-b6c7-12a2c276844a
-- title:
--   Marker Extension: exists map some of marker Free
-- statement:
--   Marker-free option words are exactly renamed source-alphabet words.
--
--   Source: https://github.com/pseudorandom/balance_and_specification/blob/62771ced95e6f431064d40780b623362263ae9e4/BalanceSpecificaton/MarkerExtension.lean#L160-L169
-- source:
--   https://github.com/pseudorandom/balance_and_specification/blob/62771ced95e6f431064d40780b623362263ae9e4/BalanceSpecificaton/MarkerExtension.lean#L160-L169

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

theorem BalanceSpecification.MarkerExtension.exists_map_some_of_markerFree {w : Word (Option A)} (hw : none ∉ w) :
    ∃ v : Word A, w = v.map some := by sorry
