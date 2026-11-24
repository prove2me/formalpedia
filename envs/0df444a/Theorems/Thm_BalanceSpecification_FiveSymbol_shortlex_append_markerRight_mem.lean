-- Prove2me | Theorems.Thm_BalanceSpecification_FiveSymbol_shortlex_append_markerRight_mem
-- name    : BalanceSpecification.FiveSymbol.shortlex_append_markerRight_mem
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T02:10:51.03129+00:00
-- url     : https://prove2.me/theorems/5911f43d-58f2-4f39-af34-56ec340a6dc2
-- title:
--   Five Symbol: shortlex append marker Right mem
-- statement:
--   The right marked extension of its indexed word remains admissible.
--
--   Source: https://github.com/pseudorandom/balance_and_specification/blob/62771ced95e6f431064d40780b623362263ae9e4/BalanceSpecificaton/FiveSymbol.lean#L451-L524
-- source:
--   https://github.com/pseudorandom/balance_and_specification/blob/62771ced95e6f431064d40780b623362263ae9e4/BalanceSpecificaton/FiveSymbol.lean#L451-L524

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

theorem BalanceSpecification.FiveSymbol.shortlex_append_markerRight_mem {j : ℕ} (_hj : 1 ≤ j)
    (hw : shortlexWord (A := Alphabet) j ∈ language shift) :
    shortlexWord j ++ markerRight j ∈ language shift := by sorry
