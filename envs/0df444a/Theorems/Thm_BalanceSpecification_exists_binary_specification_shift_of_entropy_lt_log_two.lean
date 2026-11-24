-- Prove2me | Theorems.Thm_BalanceSpecification_exists_binary_specification_shift_of_entropy_lt_log_two
-- name    : BalanceSpecification.exists_binary_specification_shift_of_entropy_lt_log_two
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T02:06:55.838796+00:00
-- url     : https://prove2.me/theorems/52f01ddb-d547-4e53-bf2b-d5e10515c9e2
-- title:
--   Balance Specification: exists binary specification shift of entropy lt log two
-- statement:
--   Every entropy in `[0, log 2)` is realized by an actual binary specification
--   shift. The positive case uses the proved renewal-pressure entropy formula.
--
--   Source: https://github.com/pseudorandom/balance_and_specification/blob/62771ced95e6f431064d40780b623362263ae9e4/BalanceSpecificaton/EntropyModel.lean#L69-L82
-- source:
--   https://github.com/pseudorandom/balance_and_specification/blob/62771ced95e6f431064d40780b623362263ae9e4/BalanceSpecificaton/EntropyModel.lean#L69-L82

module
public import Definitions.Def_BalanceSpecificaton_ProductShift
public import Definitions.Def_BalanceSpecificaton_EntropyRealization
public import Definitions.Def_BalanceSpecificaton_SGapEntropy
public import Mathlib.Tactic
public import Definitions.Def_BalanceSpecificaton_EntropyModel
set_option autoImplicit true
@[expose] public section
public section
noncomputable section
open BalanceSpecification

theorem BalanceSpecification.exists_binary_specification_shift_of_entropy_lt_log_two
    [TopologicalSpace Bool] [DiscreteTopology Bool]
    {h : ℝ} (hh : 0 ≤ h) (hsmall : h < Real.log 2) :
    ∃ Y : ShiftSpace Bool, ∃ hY : Y.carrier.Nonempty,
      HasSpecification Y ∧ entropy Y hY = h := by sorry
