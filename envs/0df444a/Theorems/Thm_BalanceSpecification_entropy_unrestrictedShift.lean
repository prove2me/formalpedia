-- Prove2me | Theorems.Thm_BalanceSpecification_entropy_unrestrictedShift
-- name    : BalanceSpecification.entropy_unrestrictedShift
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T01:43:13.237007+00:00
-- url     : https://prove2.me/theorems/86be5ad3-1cf6-4e16-a61c-af9374bdcced
-- title:
--   Balance Specification: entropy unrestricted Shift
-- statement:
--   The actual limiting word-count entropy of the full shift is the logarithm
--   of its alphabet cardinality.
--
--   Source: https://github.com/pseudorandom/balance_and_specification/blob/62771ced95e6f431064d40780b623362263ae9e4/BalanceSpecificaton/ProductShift.lean#L194-L204
-- source:
--   https://github.com/pseudorandom/balance_and_specification/blob/62771ced95e6f431064d40780b623362263ae9e4/BalanceSpecificaton/ProductShift.lean#L194-L204

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

theorem BalanceSpecification.entropy_unrestrictedShift [Fintype A] [TopologicalSpace A] [Nonempty A] :
    entropy (unrestrictedShift A) unrestrictedShift_nonempty = Real.log (Fintype.card A) := by sorry
