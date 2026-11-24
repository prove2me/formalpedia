-- Prove2me | Theorems.Thm_BalanceSpecification_FiveSymbol_arithGeom_partial_sum_identity
-- name    : BalanceSpecification.FiveSymbol.arithGeom_partial_sum_identity
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-24T02:11:58.234649+00:00
-- url     : https://prove2.me/theorems/950f9ece-fce3-4beb-8d17-906f2193c607
-- title:
--   Five Symbol: arith Geom partial sum identity
-- statement:
--   The finite arithmetic-geometric sum, proved without a convergence assumption.
--
--   Source: https://github.com/pseudorandom/balance_and_specification/blob/62771ced95e6f431064d40780b623362263ae9e4/BalanceSpecificaton/FiveSymbolBalance.lean#L299-L307
-- source:
--   https://github.com/pseudorandom/balance_and_specification/blob/62771ced95e6f431064d40780b623362263ae9e4/BalanceSpecificaton/FiveSymbolBalance.lean#L299-L307

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

theorem BalanceSpecification.FiveSymbol.arithGeom_partial_sum_identity (n : ℕ) :
    9 * (∑ l ∈ Finset.range (n + 1), (l : ℝ) * (1 / 4 : ℝ) ^ l) =
      4 - (3 * (n : ℝ) + 4) * (1 / 4 : ℝ) ^ n := by sorry
