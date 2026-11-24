-- Prove2me | Theorems.Thm_BalanceSpecification_FiveSymbol_shortlex_length_add_one_lt_markerLength
-- name    : BalanceSpecification.FiveSymbol.shortlex_length_add_one_lt_markerLength
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T02:10:23.218837+00:00
-- url     : https://prove2.me/theorems/de97d48f-aca3-43fe-be9c-eecf38ee1565
-- title:
--   Five Symbol: shortlex length add one lt marker Length
-- statement:
--   The Five Symbol construction uses the shortlex length add one lt marker Length property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/pseudorandom/balance_and_specification/blob/62771ced95e6f431064d40780b623362263ae9e4/BalanceSpecificaton/FiveSymbol.lean#L280-L284
-- source:
--   https://github.com/pseudorandom/balance_and_specification/blob/62771ced95e6f431064d40780b623362263ae9e4/BalanceSpecificaton/FiveSymbol.lean#L280-L284

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

theorem BalanceSpecification.FiveSymbol.shortlex_length_add_one_lt_markerLength {j : ℕ} (hj : 1 ≤ j) :
    (shortlexWord (A := Alphabet) j).length + 1 < markerLength j := by sorry
