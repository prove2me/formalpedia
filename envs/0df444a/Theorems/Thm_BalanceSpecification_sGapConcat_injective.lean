-- Prove2me | Theorems.Thm_BalanceSpecification_sGapConcat_injective
-- name    : BalanceSpecification.sGapConcat_injective
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-24T02:05:54.070928+00:00
-- url     : https://prove2.me/theorems/e5c172f2-d92c-411a-ae27-12854716611c
-- title:
--   Balance Specification: s Gap Concat injective
-- statement:
--   The Balance Specification construction uses the s Gap Concat injective property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/pseudorandom/balance_and_specification/blob/62771ced95e6f431064d40780b623362263ae9e4/BalanceSpecificaton/SGapRenewal.lean#L91-L93
-- source:
--   https://github.com/pseudorandom/balance_and_specification/blob/62771ced95e6f431064d40780b623362263ae9e4/BalanceSpecificaton/SGapRenewal.lean#L91-L93

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

theorem BalanceSpecification.sGapConcat_injective {r : ℕ} : Function.Injective (@sGapConcat r) := by sorry
