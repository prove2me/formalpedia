-- Prove2me | Theorems.Thm_BalanceSpecification_exists_specification_shift_of_entropy
-- name    : BalanceSpecification.exists_specification_shift_of_entropy
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-24T02:07:01.232945+00:00
-- url     : https://prove2.me/theorems/f74b96ec-ca22-4720-b797-48df6ba34f1e
-- title:
--   Balance Specification: exists specification shift of entropy
-- statement:
--   Every nonnegative real is the actual word-growth entropy of a nonempty
--   finite-alphabet shift with fixed-gap specification. This proves the model
--   existence step used in the arbitrary positive entropy construction.
--
--   Source: https://github.com/pseudorandom/balance_and_specification/blob/62771ced95e6f431064d40780b623362263ae9e4/BalanceSpecificaton/EntropyModel.lean#L87-L102
-- source:
--   https://github.com/pseudorandom/balance_and_specification/blob/62771ced95e6f431064d40780b623362263ae9e4/BalanceSpecificaton/EntropyModel.lean#L87-L102

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

theorem BalanceSpecification.exists_specification_shift_of_entropy
    [TopologicalSpace Bool] [DiscreteTopology Bool]
    {h : ℝ} (hh : 0 ≤ h) :
    ∃ n : ℕ, 1 ≤ n ∧ ∃ X : ShiftSpace (Fin n × Bool), ∃ hX : X.carrier.Nonempty,
      HasSpecification X ∧ entropy X hX = h := by sorry
