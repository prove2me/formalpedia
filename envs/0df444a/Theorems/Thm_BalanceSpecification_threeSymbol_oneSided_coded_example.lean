-- Prove2me | Theorems.Thm_BalanceSpecification_threeSymbol_oneSided_coded_example
-- name    : BalanceSpecification.threeSymbol_oneSided_coded_example
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T02:51:44.566806+00:00
-- url     : https://prove2.me/theorems/c3b9651c-3b2d-42da-91de-4898d96faa2f
-- title:
--   Balance Specification: three Symbol one Sided coded example
-- statement:
--   The graph-compatible positive-exponent coded example has entropy `log 2`,
--   is right-balanced but not left-balanced, and fails variable specification.
--   The natural-number convention is explicit in `OneSidedExample.code`.
--
--   Source: https://github.com/pseudorandom/balance_and_specification/blob/62771ced95e6f431064d40780b623362263ae9e4/BalanceSpecificaton/Examples.lean#L26-L33
-- source:
--   https://github.com/pseudorandom/balance_and_specification/blob/62771ced95e6f431064d40780b623362263ae9e4/BalanceSpecificaton/Examples.lean#L26-L33

module
public import Definitions.Def_BalanceSpecificaton_FiveSymbolBalance
public import Definitions.Def_BalanceSpecificaton_TopologicalMixing
public import Definitions.Def_BalanceSpecificaton_OneSidedBounds
public import Definitions.Def_BalanceSpecificaton_Examples
public import Theorems.Thm_BalanceSpecification_OneSidedExample_nonempty

set_option autoImplicit true
@[expose] public section
public section
open BalanceSpecification

theorem BalanceSpecification.threeSymbol_oneSided_coded_example :
    IsCoded OneSidedExample.shift ∧ Irreducible OneSidedExample.shift ∧
      entropy OneSidedExample.shift OneSidedExample.nonempty = Real.log 2 ∧
      RightBalanced (language OneSidedExample.shift) ∧
      ¬LeftBalanced (language OneSidedExample.shift) ∧
      ¬HasVariableSpecification OneSidedExample.shift := by sorry
