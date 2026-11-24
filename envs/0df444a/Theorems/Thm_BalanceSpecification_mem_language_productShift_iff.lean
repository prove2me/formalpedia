-- Prove2me | Theorems.Thm_BalanceSpecification_mem_language_productShift_iff
-- name    : BalanceSpecification.mem_language_productShift_iff
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-24T01:46:25.342806+00:00
-- url     : https://prove2.me/theorems/df14d68e-0964-4d55-9cad-8e5a86847472
-- title:
--   Balance Specification: mem language product Shift iff
-- statement:
--   Language membership in the product is exactly simultaneous membership of
--   the two projected finite words.
--
--   Source: https://github.com/pseudorandom/balance_and_specification/blob/62771ced95e6f431064d40780b623362263ae9e4/BalanceSpecificaton/ProductShift.lean#L50-L68
-- source:
--   https://github.com/pseudorandom/balance_and_specification/blob/62771ced95e6f431064d40780b623362263ae9e4/BalanceSpecificaton/ProductShift.lean#L50-L68

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

theorem BalanceSpecification.mem_language_productShift_iff [TopologicalSpace A] [TopologicalSpace B]
    {X : ShiftSpace A} {Y : ShiftSpace B} {w : Word (A × B)} :
    w ∈ language (productShift X Y) ↔
      w.map Prod.fst ∈ language X ∧ w.map Prod.snd ∈ language Y := by sorry
