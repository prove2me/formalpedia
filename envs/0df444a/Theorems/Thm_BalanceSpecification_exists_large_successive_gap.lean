-- Prove2me | Theorems.Thm_BalanceSpecification_exists_large_successive_gap
-- name    : BalanceSpecification.exists_large_successive_gap
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T01:46:54.717947+00:00
-- url     : https://prove2.me/theorems/a522fdbc-2341-4334-8a37-fec76020d555
-- title:
--   Balance Specification: exists large successive gap
-- statement:
--   Failure of boundedness supplies arbitrarily long genuine consecutive gaps.
--
--   Source: https://github.com/pseudorandom/balance_and_specification/blob/62771ced95e6f431064d40780b623362263ae9e4/BalanceSpecificaton/SGapBounds.lean#L80-L86
-- source:
--   https://github.com/pseudorandom/balance_and_specification/blob/62771ced95e6f431064d40780b623362263ae9e4/BalanceSpecificaton/SGapBounds.lean#L80-L86

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

theorem BalanceSpecification.exists_large_successive_gap {S : Set ℕ} (hS : ¬HasBoundedSuccessiveGaps S)
    (k : ℕ) : ∃ a ∈ S, ∃ b ∈ S, a < b ∧
      (∀ s ∈ S, a < s → b ≤ s) ∧ a + k < b := by sorry
