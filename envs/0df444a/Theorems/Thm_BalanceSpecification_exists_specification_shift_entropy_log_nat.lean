-- Prove2me | Theorems.Thm_BalanceSpecification_exists_specification_shift_entropy_log_nat
-- name    : BalanceSpecification.exists_specification_shift_entropy_log_nat
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-24T02:37:48.632648+00:00
-- url     : https://prove2.me/theorems/7f23c98e-76bd-4abe-9cbc-af48a3437e5f
-- title:
--   Balance Specification: exists specification shift entropy log nat
-- statement:
--   The zero-residual case is an actual full shift times a one-point shift on
--   the same binary factor used in the positive-residual construction.
--
--   Source: https://github.com/pseudorandom/balance_and_specification/blob/62771ced95e6f431064d40780b623362263ae9e4/BalanceSpecificaton/EntropyModel.lean#L53-L65
-- source:
--   https://github.com/pseudorandom/balance_and_specification/blob/62771ced95e6f431064d40780b623362263ae9e4/BalanceSpecificaton/EntropyModel.lean#L53-L65

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

theorem BalanceSpecification.exists_specification_shift_entropy_log_nat
    [TopologicalSpace Bool] [DiscreteTopology Bool] (n : ℕ) (hn : 1 ≤ n) :
    ∃ X : ShiftSpace (Fin n × Bool), ∃ hX : X.carrier.Nonempty,
      HasSpecification X ∧ entropy X hX = Real.log n := by sorry
