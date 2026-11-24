-- Prove2me | Theorems.Thm_BalanceSpecification_hasBoundedSuccessiveGaps_of_finite
-- name    : BalanceSpecification.hasBoundedSuccessiveGaps_of_finite
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T01:58:17.312985+00:00
-- url     : https://prove2.me/theorems/75576ef5-9a2a-41ea-8cc1-59e2b7458cec
-- title:
--   Balance Specification: has Bounded Successive Gaps of finite
-- statement:
--   Finite sets have bounded consecutive differences, even when no consecutive
--   pair exists.
--
--   Source: https://github.com/pseudorandom/balance_and_specification/blob/62771ced95e6f431064d40780b623362263ae9e4/BalanceSpecificaton/SGapBounds.lean#L71-L77
-- source:
--   https://github.com/pseudorandom/balance_and_specification/blob/62771ced95e6f431064d40780b623362263ae9e4/BalanceSpecificaton/SGapBounds.lean#L71-L77

module
public import Mathlib.Data.Finset.Max
public import Mathlib.Data.Set.Finite.Lattice
public import Mathlib.Tactic
public import Definitions.Def_BalanceSpecificaton_SGapBounds
set_option autoImplicit true
@[expose] public section
public section
noncomputable section
open BalanceSpecification

theorem BalanceSpecification.hasBoundedSuccessiveGaps_of_finite {S : Set ℕ} (hS : S.Finite) :
    HasBoundedSuccessiveGaps S := by sorry
