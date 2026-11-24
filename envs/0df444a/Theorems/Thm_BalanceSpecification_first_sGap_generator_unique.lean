-- Prove2me | Theorems.Thm_BalanceSpecification_first_sGap_generator_unique
-- name    : BalanceSpecification.first_sGap_generator_unique
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-24T01:47:27.860165+00:00
-- url     : https://prove2.me/theorems/78c0f8a1-e9de-4d9a-a914-f2ededa2e2ee
-- title:
--   Balance Specification: first s Gap generator unique
-- statement:
--   The first complete gap in a concatenation is uniquely determined by its word.
--
--   Source: https://github.com/pseudorandom/balance_and_specification/blob/62771ced95e6f431064d40780b623362263ae9e4/BalanceSpecificaton/SGapRenewal.lean#L32-L46
-- source:
--   https://github.com/pseudorandom/balance_and_specification/blob/62771ced95e6f431064d40780b623362263ae9e4/BalanceSpecificaton/SGapRenewal.lean#L32-L46

module
public import Definitions.Def_BalanceSpecificaton_SGap
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.BigOperators.Group.List.Defs
public import Mathlib.Tactic
public import Definitions.Def_BalanceSpecificaton_SGapRenewal
set_option autoImplicit true
@[expose] public section
public section
noncomputable section
open BalanceSpecification

theorem BalanceSpecification.first_sGap_generator_unique {s t : ℕ} {u v : Word Bool}
    (hu : u = [] ∨ ∃ z, u = true :: z)
    (hv : v = [] ∨ ∃ z, v = true :: z)
    (h : (true :: List.replicate s false) ++ u =
      (true :: List.replicate t false) ++ v) : s = t ∧ u = v := by sorry
