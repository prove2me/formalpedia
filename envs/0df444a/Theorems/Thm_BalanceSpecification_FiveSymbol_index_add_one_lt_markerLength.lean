-- Prove2me | Theorems.Thm_BalanceSpecification_FiveSymbol_index_add_one_lt_markerLength
-- name    : BalanceSpecification.FiveSymbol.index_add_one_lt_markerLength
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-24T02:10:25.356613+00:00
-- url     : https://prove2.me/theorems/fe81ede1-5bb8-418f-955a-d1320efc7311
-- title:
--   Five Symbol: index add one lt marker Length
-- statement:
--   The Five Symbol construction uses the index add one lt marker Length property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/pseudorandom/balance_and_specification/blob/62771ced95e6f431064d40780b623362263ae9e4/BalanceSpecificaton/FiveSymbol.lean#L273-L278
-- source:
--   https://github.com/pseudorandom/balance_and_specification/blob/62771ced95e6f431064d40780b623362263ae9e4/BalanceSpecificaton/FiveSymbol.lean#L273-L278

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

theorem BalanceSpecification.FiveSymbol.index_add_one_lt_markerLength {j : ℕ} (hj : 1 ≤ j) : j + 1 < markerLength j := by sorry
