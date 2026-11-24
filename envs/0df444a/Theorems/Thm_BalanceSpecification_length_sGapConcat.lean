-- Prove2me | Theorems.Thm_BalanceSpecification_length_sGapConcat
-- name    : BalanceSpecification.length_sGapConcat
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T02:35:09.615131+00:00
-- url     : https://prove2.me/theorems/a97fadda-1654-4038-b744-db9f8bd37ddf
-- title:
--   Balance Specification: length s Gap Concat
-- statement:
--   The Balance Specification construction uses the length s Gap Concat property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/pseudorandom/balance_and_specification/blob/62771ced95e6f431064d40780b623362263ae9e4/BalanceSpecificaton/SGapRenewal.lean#L95-L99
-- source:
--   https://github.com/pseudorandom/balance_and_specification/blob/62771ced95e6f431064d40780b623362263ae9e4/BalanceSpecificaton/SGapRenewal.lean#L95-L99

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

theorem BalanceSpecification.length_sGapConcat {r : ℕ} (f : Fin r → ℕ) :
    (sGapConcat f).length = ∑ i : Fin r, (f i + 1) := by sorry
