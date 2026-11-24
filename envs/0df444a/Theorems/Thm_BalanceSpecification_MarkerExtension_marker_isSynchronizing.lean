-- Prove2me | Theorems.Thm_BalanceSpecification_MarkerExtension_marker_isSynchronizing
-- name    : BalanceSpecification.MarkerExtension.marker_isSynchronizing
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-24T02:01:38.860539+00:00
-- url     : https://prove2.me/theorems/7eeb2f8a-6fdf-4c18-b8f3-1162c74d9ad2
-- title:
--   Marker Extension: marker is Synchronizing
-- statement:
--   The fresh marker is genuinely synchronizing in every nonempty marked code.
--
--   Source: https://github.com/pseudorandom/balance_and_specification/blob/62771ced95e6f431064d40780b623362263ae9e4/BalanceSpecificaton/MarkerExtension.lean#L204-L228
-- source:
--   https://github.com/pseudorandom/balance_and_specification/blob/62771ced95e6f431064d40780b623362263ae9e4/BalanceSpecificaton/MarkerExtension.lean#L204-L228

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
variable [TopologicalSpace A] [DiscreteTopology A] [Fintype A]
  [TopologicalSpace (Option A)] [DiscreteTopology (Option A)]
omit [TopologicalSpace A] [DiscreteTopology A] [Fintype A]

theorem BalanceSpecification.MarkerExtension.marker_isSynchronizing {P : Set (Word A)} (hP : P.Nonempty) :
    IsSynchronizing (language (codedShift (markedCode P))) [none] := by sorry
