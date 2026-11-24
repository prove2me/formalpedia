-- Prove2me | Theorems.Thm_BalanceSpecification_sGapListConcat_injective
-- name    : BalanceSpecification.sGapListConcat_injective
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T02:05:56.427864+00:00
-- url     : https://prove2.me/theorems/719682de-0670-4339-8fdb-11ffd1207720
-- title:
--   Balance Specification: s Gap List Concat injective
-- statement:
--   The Balance Specification construction uses the s Gap List Concat injective property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/pseudorandom/balance_and_specification/blob/62771ced95e6f431064d40780b623362263ae9e4/BalanceSpecificaton/SGapRenewal.lean#L71-L86
-- source:
--   https://github.com/pseudorandom/balance_and_specification/blob/62771ced95e6f431064d40780b623362263ae9e4/BalanceSpecificaton/SGapRenewal.lean#L71-L86

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

theorem BalanceSpecification.sGapListConcat_injective : Function.Injective sGapListConcat := by sorry
