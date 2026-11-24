-- Prove2me | Theorems.Thm_BalanceSpecification_wordCount_le_of_marker_extension
-- name    : BalanceSpecification.wordCount_le_of_marker_extension
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-24T02:04:21.778234+00:00
-- url     : https://prove2.me/theorems/f2061ff4-ec2b-4aa4-b920-40af11787700
-- title:
--   Balance Specification: word Count le of marker extension
-- statement:
--   Marker extensions include an injective copy of every length of the base language.
--
--   Source: https://github.com/pseudorandom/balance_and_specification/blob/62771ced95e6f431064d40780b623362263ae9e4/BalanceSpecificaton/MarkerNonleft.lean#L93-L104
-- source:
--   https://github.com/pseudorandom/balance_and_specification/blob/62771ced95e6f431064d40780b623362263ae9e4/BalanceSpecificaton/MarkerNonleft.lean#L93-L104

module
public import Definitions.Def_BalanceSpecificaton_MarkerExtension
public import Definitions.Def_BalanceSpecificaton_TwoSidedCounts
public import Mathlib.Tactic
public import Definitions.Def_BalanceSpecificaton_MarkerNonleft
set_option autoImplicit true
@[expose] public section
public section
noncomputable section
open BalanceSpecification
variable {A : Type*} [Fintype A] [TopologicalSpace A] [TopologicalSpace (Option A)]

theorem BalanceSpecification.wordCount_le_of_marker_extension {X : ShiftSpace (Option A)} {Y : ShiftSpace A}
    (hext : ∀ v ∈ language Y, none :: v.map some ∈ language X) (n : ℕ) :
    wordCount (language Y) n ≤ wordCount (language X) n := by sorry
