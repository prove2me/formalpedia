-- Prove2me | Theorems.Thm_BalanceSpecification_GapRead_decompose_markers
-- name    : BalanceSpecification.GapRead.decompose_markers
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T02:06:12.445468+00:00
-- url     : https://prove2.me/theorems/88638753-839d-48ce-82d8-5701a17f6408
-- title:
--   Gap Read: decompose markers
-- statement:
--   Between the first and last markers, a finite S-gap path is a completed renewal word.
--
--   Source: https://github.com/pseudorandom/balance_and_specification/blob/62771ced95e6f431064d40780b623362263ae9e4/BalanceSpecificaton/SGapRenewal.lean#L243-L266
-- source:
--   https://github.com/pseudorandom/balance_and_specification/blob/62771ced95e6f431064d40780b623362263ae9e4/BalanceSpecificaton/SGapRenewal.lean#L243-L266

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

theorem BalanceSpecification.GapRead.decompose_markers {S : Set ℕ} {a b : ℕ} {w : Word Bool}
    (h : GapRead S a w b) (ht : true ∈ w) :
    ∃ v : Word Bool, ∃ m : ℕ, v ∈ generatedWords (sGapCode S) ∧
      w = List.replicate a false ++ v ++ true :: List.replicate m false := by sorry
