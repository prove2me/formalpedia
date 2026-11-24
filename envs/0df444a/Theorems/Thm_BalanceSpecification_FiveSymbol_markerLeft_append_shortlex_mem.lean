-- Prove2me | Theorems.Thm_BalanceSpecification_FiveSymbol_markerLeft_append_shortlex_mem
-- name    : BalanceSpecification.FiveSymbol.markerLeft_append_shortlex_mem
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-24T02:10:40.429542+00:00
-- url     : https://prove2.me/theorems/ab68109f-5a67-42a7-85f8-bd9936c91280
-- title:
--   Five Symbol: marker Left append shortlex mem
-- statement:
--   The left marked extension of its indexed word remains admissible.
--
--   Source: https://github.com/pseudorandom/balance_and_specification/blob/62771ced95e6f431064d40780b623362263ae9e4/BalanceSpecificaton/FiveSymbol.lean#L387-L437
-- source:
--   https://github.com/pseudorandom/balance_and_specification/blob/62771ced95e6f431064d40780b623362263ae9e4/BalanceSpecificaton/FiveSymbol.lean#L387-L437

module
public import Definitions.Def_BalanceSpecificaton_Shortlex
public import Definitions.Def_BalanceSpecificaton_Forbidden
public import Definitions.Def_BalanceSpecificaton_Synchronization
public import Mathlib.Tactic
public import Definitions.Def_BalanceSpecificaton_FiveSymbol
set_option autoImplicit true
@[expose] public section
public section
noncomputable section
open BalanceSpecification BalanceSpecification.FiveSymbol

theorem BalanceSpecification.FiveSymbol.markerLeft_append_shortlex_mem {j : ℕ} (_hj : 1 ≤ j)
    (hw : shortlexWord (A := Alphabet) j ∈ language shift) :
    markerLeft j ++ shortlexWord j ∈ language shift := by sorry
