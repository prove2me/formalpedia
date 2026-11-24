-- Prove2me | Theorems.Thm_BalanceSpecification_centered_block_eq_of_le
-- name    : BalanceSpecification.centered_block_eq_of_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T01:45:39.057234+00:00
-- url     : https://prove2.me/theorems/d5553179-173c-49b9-8867-9bf398058fe0
-- title:
--   Balance Specification: centered block eq of le
-- statement:
--   A larger centered block determines every smaller centered block.
--
--   Source: https://github.com/pseudorandom/balance_and_specification/blob/62771ced95e6f431064d40780b623362263ae9e4/BalanceSpecificaton/CylinderAlgebra.lean#L24-L42
-- source:
--   https://github.com/pseudorandom/balance_and_specification/blob/62771ced95e6f431064d40780b623362263ae9e4/BalanceSpecificaton/CylinderAlgebra.lean#L24-L42

module
public import Definitions.Def_BalanceSpecificaton_Measures
public import Mathlib.MeasureTheory.Measure.MeasuredSets
public import Mathlib.MeasureTheory.SetAlgebra
public import Mathlib.Tactic
public import Definitions.Def_BalanceSpecificaton_CylinderAlgebra
set_option autoImplicit true
@[expose] public section
public section
noncomputable section
open MeasureTheory Set MeasurableSpace
open scoped symmDiff ENNReal
open BalanceSpecification
variable {A : Type*}

theorem BalanceSpecification.centered_block_eq_of_le {n N : ℕ} (hn : n ≤ N)
    {x y : Configuration A}
    (h : block x (-(N : ℤ)) (2 * N + 1) =
      block y (-(N : ℤ)) (2 * N + 1)) :
    block x (-(n : ℤ)) (2 * n + 1) = block y (-(n : ℤ)) (2 * n + 1) := by sorry
