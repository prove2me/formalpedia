-- Prove2me | Theorems.Thm_BalanceSpecification_entropy_unrestrictedShift_of_unique
-- name    : BalanceSpecification.entropy_unrestrictedShift_of_unique
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T02:30:48.306394+00:00
-- url     : https://prove2.me/theorems/2b73b3f9-821d-4c53-a6f0-9af7011d742f
-- title:
--   Balance Specification: entropy unrestricted Shift of unique
-- statement:
--   A full shift on a singleton alphabet is the required zero-entropy
--   specification system.
--
--   Source: https://github.com/pseudorandom/balance_and_specification/blob/62771ced95e6f431064d40780b623362263ae9e4/BalanceSpecificaton/ProductShift.lean#L208-L210
-- source:
--   https://github.com/pseudorandom/balance_and_specification/blob/62771ced95e6f431064d40780b623362263ae9e4/BalanceSpecificaton/ProductShift.lean#L208-L210

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

theorem BalanceSpecification.entropy_unrestrictedShift_of_unique [Fintype A] [TopologicalSpace A] [Unique A] :
    entropy (unrestrictedShift A) unrestrictedShift_nonempty = 0 := by sorry
