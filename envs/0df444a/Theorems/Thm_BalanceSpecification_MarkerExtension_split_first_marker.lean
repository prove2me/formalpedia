-- Prove2me | Theorems.Thm_BalanceSpecification_MarkerExtension_split_first_marker
-- name    : BalanceSpecification.MarkerExtension.split_first_marker
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-24T02:01:40.371779+00:00
-- url     : https://prove2.me/theorems/f6c4c56a-7628-4462-9621-76a3c161af32
-- title:
--   Marker Extension: split first marker
-- statement:
--   Split a word just before its first fresh marker.
--
--   Source: https://github.com/pseudorandom/balance_and_specification/blob/62771ced95e6f431064d40780b623362263ae9e4/BalanceSpecificaton/MarkerExtension.lean#L172-L183
-- source:
--   https://github.com/pseudorandom/balance_and_specification/blob/62771ced95e6f431064d40780b623362263ae9e4/BalanceSpecificaton/MarkerExtension.lean#L172-L183

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

theorem BalanceSpecification.MarkerExtension.split_first_marker (w : Word (Option A)) :
    ∃ a : Word A, ∃ b : Word (Option A),
      w = a.map some ++ b ∧ (b = [] ∨ ∃ t, b = none :: t) := by sorry
