-- Prove2me | Theorems.Thm_BalanceSpecification_sGap_language_decomposition
-- name    : BalanceSpecification.sGap_language_decomposition
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T01:47:37.718249+00:00
-- url     : https://prove2.me/theorems/fef875c0-61e9-45f5-8612-41a6f43823e5
-- title:
--   Balance Specification: s Gap language decomposition
-- statement:
--   A language word is either all zeros or a zero prefix, completed renewal word,
--   last marker, and zero suffix.
--
--   Source: https://github.com/pseudorandom/balance_and_specification/blob/62771ced95e6f431064d40780b623362263ae9e4/BalanceSpecificaton/SGapRenewal.lean#L270-L280
-- source:
--   https://github.com/pseudorandom/balance_and_specification/blob/62771ced95e6f431064d40780b623362263ae9e4/BalanceSpecificaton/SGapRenewal.lean#L270-L280

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

theorem BalanceSpecification.sGap_language_decomposition [TopologicalSpace Bool] [DiscreteTopology Bool]
    {S : Set ℕ} (hS : S.Nonempty) {w : Word Bool}
    (hw : w ∈ language (sGapShift S)) :
    w = List.replicate w.length false ∨
      ∃ a m : ℕ, ∃ v : Word Bool, v ∈ generatedWords (sGapCode S) ∧
        w = List.replicate a false ++ v ++ true :: List.replicate m false := by sorry
