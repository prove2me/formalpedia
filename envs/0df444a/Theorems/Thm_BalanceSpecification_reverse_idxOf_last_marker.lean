-- Prove2me | Theorems.Thm_BalanceSpecification_reverse_idxOf_last_marker
-- name    : BalanceSpecification.reverse_idxOf_last_marker
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T02:04:17.919841+00:00
-- url     : https://prove2.me/theorems/961959d7-7bfe-48d1-8eb0-1fc4055e3c14
-- title:
--   Balance Specification: reverse idx Of last marker
-- statement:
--   The last marker can be read from a word by the first marker in its reverse.
--
--   Source: https://github.com/pseudorandom/balance_and_specification/blob/62771ced95e6f431064d40780b623362263ae9e4/BalanceSpecificaton/MarkerNonleft.lean#L20-L27
-- source:
--   https://github.com/pseudorandom/balance_and_specification/blob/62771ced95e6f431064d40780b623362263ae9e4/BalanceSpecificaton/MarkerNonleft.lean#L20-L27

module
public import Definitions.Def_BalanceSpecificaton_MarkerExtension
public import Definitions.Def_BalanceSpecificaton_TwoSidedCounts
public import Mathlib.Tactic
public import Definitions.Def_BalanceSpecificaton_MarkerNonleft
set_option autoImplicit true
@[expose] public section
public section
noncomputable section
open BalanceSpecification
variable {A : Type*} [Fintype A] [TopologicalSpace A] [TopologicalSpace (Option A)]
omit [Fintype A] [TopologicalSpace A] [TopologicalSpace (Option A)]

theorem BalanceSpecification.reverse_idxOf_last_marker [DecidableEq A] (p : Word (Option A)) (v : Word A) :
    ((p ++ [none] ++ v.map some).reverse).idxOf none = v.length := by sorry
