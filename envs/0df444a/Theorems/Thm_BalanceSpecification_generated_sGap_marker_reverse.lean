-- Prove2me | Theorems.Thm_BalanceSpecification_generated_sGap_marker_reverse
-- name    : BalanceSpecification.generated_sGap_marker_reverse
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-24T02:05:26.319195+00:00
-- url     : https://prove2.me/theorems/4853af0d-79ad-4b62-a6b4-65e8258ff7fa
-- title:
--   Balance Specification: generated s Gap marker reverse
-- statement:
--   The Balance Specification construction uses the generated s Gap marker reverse property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/pseudorandom/balance_and_specification/blob/62771ced95e6f431064d40780b623362263ae9e4/BalanceSpecificaton/SGap.lean#L377-L395
-- source:
--   https://github.com/pseudorandom/balance_and_specification/blob/62771ced95e6f431064d40780b623362263ae9e4/BalanceSpecificaton/SGap.lean#L377-L395

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

theorem BalanceSpecification.generated_sGap_marker_reverse {S : Set ℕ} {w : Word Bool}
    (hw : w ∈ generatedWords (sGapCode S)) :
    ∃ r ∈ generatedWords (sGapCode S), [true] ++ w.reverse = r ++ [true] := by sorry
