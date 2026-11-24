-- Prove2me | Theorems.Thm_BalanceSpecification_MarkerExtension_markerFree_prefix_split
-- name    : BalanceSpecification.MarkerExtension.markerFree_prefix_split
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T02:01:07.55728+00:00
-- url     : https://prove2.me/theorems/75d4f1d8-7ed9-40ac-9554-349754f9bb3a
-- title:
--   Marker Extension: marker Free prefix split
-- statement:
--   A marker occurring after a marker-free prefix must lie in the remaining tail.
--
--   Source: https://github.com/pseudorandom/balance_and_specification/blob/62771ced95e6f431064d40780b623362263ae9e4/BalanceSpecificaton/MarkerExtension.lean#L29-L45
-- source:
--   https://github.com/pseudorandom/balance_and_specification/blob/62771ced95e6f431064d40780b623362263ae9e4/BalanceSpecificaton/MarkerExtension.lean#L29-L45

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

theorem BalanceSpecification.MarkerExtension.markerFree_prefix_split {s t p q : Word (Option A)}
    (hs : none ∉ s) (heq : s ++ t = p ++ none :: q) :
    ∃ r : Word (Option A), p = s ++ r ∧ t = r ++ none :: q := by sorry
