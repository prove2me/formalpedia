-- Prove2me | Theorems.Thm_BalanceSpecification_specification_bridge_of_le
-- name    : BalanceSpecification.specification_bridge_of_le
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-24T01:57:56.864293+00:00
-- url     : https://prove2.me/theorems/dd0c8c4a-0f73-40a9-adae-25e665310e1d
-- title:
--   Balance Specification: specification bridge of le
-- statement:
--   Once a specification gap works, every larger gap works. Extra length is
--   taken from an actual right extension of the first word.
--
--   Source: https://github.com/pseudorandom/balance_and_specification/blob/62771ced95e6f431064d40780b623362263ae9e4/BalanceSpecificaton/ProductShift.lean#L115-L130
-- source:
--   https://github.com/pseudorandom/balance_and_specification/blob/62771ced95e6f431064d40780b623362263ae9e4/BalanceSpecificaton/ProductShift.lean#L115-L130

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

theorem BalanceSpecification.specification_bridge_of_le [TopologicalSpace A] {X : ShiftSpace A}
    {N M : ℕ}
    (hN : ∀ u ∈ language X, ∀ v ∈ language X,
      ∃ w ∈ language X, w.length = N ∧ u ++ w ++ v ∈ language X)
    (hNM : N ≤ M) :
    ∀ u ∈ language X, ∀ v ∈ language X,
      ∃ w ∈ language X, w.length = M ∧ u ++ w ++ v ∈ language X := by sorry
