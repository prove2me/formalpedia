-- Prove2me | Theorems.Thm_BalanceSpecification_FiveSymbol_arithGeom_partial_sum_le
-- name    : BalanceSpecification.FiveSymbol.arithGeom_partial_sum_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T02:12:11.459813+00:00
-- url     : https://prove2.me/theorems/a47591a2-18b4-440f-96a3-7518a838d64d
-- title:
--   Five Symbol: arith Geom partial sum le
-- statement:
--   The Five Symbol construction uses the arith Geom partial sum le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/pseudorandom/balance_and_specification/blob/62771ced95e6f431064d40780b623362263ae9e4/BalanceSpecificaton/FiveSymbolBalance.lean#L309-L321
-- source:
--   https://github.com/pseudorandom/balance_and_specification/blob/62771ced95e6f431064d40780b623362263ae9e4/BalanceSpecificaton/FiveSymbolBalance.lean#L309-L321

module
public import Definitions.Def_BalanceSpecificaton_FiveSymbol
public import Definitions.Def_BalanceSpecificaton_CountBounds
public import Mathlib.Tactic
public import Definitions.Def_BalanceSpecificaton_FiveSymbolBalance
set_option autoImplicit true
@[expose] public section
public section
noncomputable section
open BalanceSpecification BalanceSpecification.FiveSymbol

theorem BalanceSpecification.FiveSymbol.arithGeom_partial_sum_le (n : ℕ) :
    (∑ l ∈ Finset.Icc 1 n, (l : ℝ) * (1 / 4 : ℝ) ^ l) ≤ 4 / 9 := by sorry
