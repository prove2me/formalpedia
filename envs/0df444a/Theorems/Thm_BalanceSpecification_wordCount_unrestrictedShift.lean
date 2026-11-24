-- Prove2me | Theorems.Thm_BalanceSpecification_wordCount_unrestrictedShift
-- name    : BalanceSpecification.wordCount_unrestrictedShift
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T01:57:59.288843+00:00
-- url     : https://prove2.me/theorems/70767bb8-aadd-48c3-8d83-d8e14ea5243b
-- title:
--   Balance Specification: word Count unrestricted Shift
-- statement:
--   All length-`n` words occur in the full shift.
--
--   Source: https://github.com/pseudorandom/balance_and_specification/blob/62771ced95e6f431064d40780b623362263ae9e4/BalanceSpecificaton/ProductShift.lean#L176-L182
-- source:
--   https://github.com/pseudorandom/balance_and_specification/blob/62771ced95e6f431064d40780b623362263ae9e4/BalanceSpecificaton/ProductShift.lean#L176-L182

module
public import Definitions.Def_BalanceSpecificaton_Periodicity
public import Definitions.Def_BalanceSpecificaton_TilingBounds
public import Mathlib.Tactic
public import Definitions.Def_BalanceSpecificaton_ProductShift
set_option autoImplicit true
@[expose] public section
public section
noncomputable section
open BalanceSpecification
open Filter
open scoped Topology
variable {A B : Type*}

theorem BalanceSpecification.wordCount_unrestrictedShift [Fintype A] [TopologicalSpace A] [Nonempty A] (n : ℕ) :
    wordCount (language (unrestrictedShift A)) n = (Fintype.card A) ^ n := by sorry
