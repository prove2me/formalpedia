-- Prove2me | Theorems.Thm_BalanceSpecification_entropy_productShift
-- name    : BalanceSpecification.entropy_productShift
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-24T01:46:32.092371+00:00
-- url     : https://prove2.me/theorems/978807b6-6ba1-4629-a72b-2e10b48d0272
-- title:
--   Balance Specification: entropy product Shift
-- statement:
--   Actual word-growth entropy adds under products.
--
--   Source: https://github.com/pseudorandom/balance_and_specification/blob/62771ced95e6f431064d40780b623362263ae9e4/BalanceSpecificaton/ProductShift.lean#L98-L111
-- source:
--   https://github.com/pseudorandom/balance_and_specification/blob/62771ced95e6f431064d40780b623362263ae9e4/BalanceSpecificaton/ProductShift.lean#L98-L111

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

theorem BalanceSpecification.entropy_productShift [Fintype A] [Fintype B]
    [TopologicalSpace A] [TopologicalSpace B] {X : ShiftSpace A} {Y : ShiftSpace B}
    (hX : X.carrier.Nonempty) (hY : Y.carrier.Nonempty) :
    entropy (productShift X Y) (productShift_nonempty hX hY) = entropy X hX + entropy Y hY := by sorry
