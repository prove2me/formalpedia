-- Prove2me | Theorems.Thm_BalanceSpecification_zeros_marker_prefix_ne
-- name    : BalanceSpecification.zeros_marker_prefix_ne
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-24T02:05:52.089439+00:00
-- url     : https://prove2.me/theorems/6550d903-3614-4795-b2f3-344978f462c9
-- title:
--   Balance Specification: zeros marker prefix ne
-- statement:
--   A shorter zero prefix followed by a marker cannot equal a longer zero prefix.
--
--   Source: https://github.com/pseudorandom/balance_and_specification/blob/62771ced95e6f431064d40780b623362263ae9e4/BalanceSpecificaton/SGapRenewal.lean#L17-L29
-- source:
--   https://github.com/pseudorandom/balance_and_specification/blob/62771ced95e6f431064d40780b623362263ae9e4/BalanceSpecificaton/SGapRenewal.lean#L17-L29

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

theorem BalanceSpecification.zeros_marker_prefix_ne {s t : ℕ} (hst : s < t) {u v : Word Bool}
    (hu : u = [] ∨ ∃ z, u = true :: z) :
    List.replicate s false ++ u ≠ List.replicate t false ++ v := by sorry
