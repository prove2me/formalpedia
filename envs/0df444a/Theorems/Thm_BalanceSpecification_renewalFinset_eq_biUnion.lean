-- Prove2me | Theorems.Thm_BalanceSpecification_renewalFinset_eq_biUnion
-- name    : BalanceSpecification.renewalFinset_eq_biUnion
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T02:06:06.091487+00:00
-- url     : https://prove2.me/theorems/8290e2ca-ed6e-493e-b6da-aae1ffcfff51
-- title:
--   Balance Specification: renewal Finset eq bi Union
-- statement:
--   Unique first-gap decomposition of the finite renewal words.
--
--   Source: https://github.com/pseudorandom/balance_and_specification/blob/62771ced95e6f431064d40780b623362263ae9e4/BalanceSpecificaton/SGapRenewal.lean#L158-L186
-- source:
--   https://github.com/pseudorandom/balance_and_specification/blob/62771ced95e6f431064d40780b623362263ae9e4/BalanceSpecificaton/SGapRenewal.lean#L158-L186

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

theorem BalanceSpecification.renewalFinset_eq_biUnion (S : Set ℕ) {n : ℕ} (hn : 0 < n) :
    renewalFinset S n = (renewalGaps S n).biUnion (renewalPiece S n) := by sorry
