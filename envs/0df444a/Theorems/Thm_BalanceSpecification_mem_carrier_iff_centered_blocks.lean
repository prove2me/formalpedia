-- Prove2me | Theorems.Thm_BalanceSpecification_mem_carrier_iff_centered_blocks
-- name    : BalanceSpecification.mem_carrier_iff_centered_blocks
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-24T02:14:15.865594+00:00
-- url     : https://prove2.me/theorems/0c04cbca-a660-4f07-80bd-7525bd1020ef
-- title:
--   Balance Specification: mem carrier iff centered blocks
-- statement:
--   Centered contiguous blocks alone determine membership in a closed shift.
--
--   Source: https://github.com/pseudorandom/balance_and_specification/blob/62771ced95e6f431064d40780b623362263ae9e4/BalanceSpecificaton/GibbsEntropyMinimal.lean#L35-L65
-- source:
--   https://github.com/pseudorandom/balance_and_specification/blob/62771ced95e6f431064d40780b623362263ae9e4/BalanceSpecificaton/GibbsEntropyMinimal.lean#L35-L65

module
public import Definitions.Def_BalanceSpecificaton_CylinderAlgebra
public import Definitions.Def_BalanceSpecificaton_EntropyMinimal
public import Mathlib.Dynamics.Ergodic.Ergodic
public import Mathlib.Tactic
public import Definitions.Def_BalanceSpecificaton_GibbsEntropyMinimal
set_option autoImplicit true
@[expose] public section
public section
noncomputable section
open MeasureTheory Set Filter
open scoped Topology
open BalanceSpecification
variable {A : Type*} [TopologicalSpace A]

theorem BalanceSpecification.mem_carrier_iff_centered_blocks {Y : ShiftSpace A} {x : Configuration A} :
    x ∈ Y.carrier ↔ ∀ n : ℕ, block x (-(n : ℤ)) (2 * n + 1) ∈ language Y := by sorry
