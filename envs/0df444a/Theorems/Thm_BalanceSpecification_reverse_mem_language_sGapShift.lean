-- Prove2me | Theorems.Thm_BalanceSpecification_reverse_mem_language_sGapShift
-- name    : BalanceSpecification.reverse_mem_language_sGapShift
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T02:05:27.302351+00:00
-- url     : https://prove2.me/theorems/d0b50801-926a-4ab4-8999-de6adf9496a4
-- title:
--   Balance Specification: reverse mem language s Gap Shift
-- statement:
--   The Balance Specification construction uses the reverse mem language s Gap Shift property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/pseudorandom/balance_and_specification/blob/62771ced95e6f431064d40780b623362263ae9e4/BalanceSpecificaton/SGap.lean#L397-L410
-- source:
--   https://github.com/pseudorandom/balance_and_specification/blob/62771ced95e6f431064d40780b623362263ae9e4/BalanceSpecificaton/SGap.lean#L397-L410

module
public import Definitions.Def_BalanceSpecificaton_CodedLanguage
public import Definitions.Def_BalanceSpecificaton_Periodicity
public import Definitions.Def_BalanceSpecificaton_SGapBounds
public import Mathlib.Tactic
public import Definitions.Def_BalanceSpecificaton_SGap
set_option autoImplicit true
@[expose] public section
public section
open BalanceSpecification

theorem BalanceSpecification.reverse_mem_language_sGapShift [TopologicalSpace Bool] [DiscreteTopology Bool]
    {S : Set ℕ} (hS : S.Nonempty) {w : Word Bool}
    (hw : w ∈ language (sGapShift S)) : w.reverse ∈ language (sGapShift S) := by sorry
