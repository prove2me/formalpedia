-- Prove2me | Theorems.Thm_BalanceSpecification_mem_language_sGapShift_iff
-- name    : BalanceSpecification.mem_language_sGapShift_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T01:39:11.989802+00:00
-- url     : https://prove2.me/theorems/8d5360ad-a7a4-422f-84fd-308c1865f5e6
-- title:
--   Balance Specification: mem language s Gap Shift iff
-- statement:
--   Exact finite-path characterization of the language of the literal coded
--   shift. No recognition property is assumed in place of the coded construction.
--
--   Source: https://github.com/pseudorandom/balance_and_specification/blob/62771ced95e6f431064d40780b623362263ae9e4/BalanceSpecificaton/SGap.lean#L148-L170
-- source:
--   https://github.com/pseudorandom/balance_and_specification/blob/62771ced95e6f431064d40780b623362263ae9e4/BalanceSpecificaton/SGap.lean#L148-L170

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

theorem BalanceSpecification.mem_language_sGapShift_iff [TopologicalSpace Bool] [DiscreteTopology Bool]
    {S : Set ℕ} (hS : S.Nonempty) {w : Word Bool} :
    w ∈ language (sGapShift S) ↔ ∃ a b, GapState S a ∧ GapRead S a w b := by sorry
