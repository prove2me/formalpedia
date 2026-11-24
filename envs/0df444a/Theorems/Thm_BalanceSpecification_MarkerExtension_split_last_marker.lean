-- Prove2me | Theorems.Thm_BalanceSpecification_MarkerExtension_split_last_marker
-- name    : BalanceSpecification.MarkerExtension.split_last_marker
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-24T02:01:33.511663+00:00
-- url     : https://prove2.me/theorems/0648f6f6-14b1-4d8f-8d4a-5a168cee3cbd
-- title:
--   Marker Extension: split last marker
-- statement:
--   Split a word immediately after its last marker, or recognize that no marker
--   is present.
--
--   Source: https://github.com/pseudorandom/balance_and_specification/blob/62771ced95e6f431064d40780b623362263ae9e4/BalanceSpecificaton/MarkerExtension.lean#L187-L197
-- source:
--   https://github.com/pseudorandom/balance_and_specification/blob/62771ced95e6f431064d40780b623362263ae9e4/BalanceSpecificaton/MarkerExtension.lean#L187-L197

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

theorem BalanceSpecification.MarkerExtension.split_last_marker (w : Word (Option A)) :
    (∃ v : Word A, w = v.map some) ∨
      ∃ u : Word (Option A), ∃ v : Word A, w = u ++ none :: v.map some := by sorry
