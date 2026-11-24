-- Prove2me | Theorems.Thm_BalanceSpecification_fiveSymbol_mixing_biBalanced_not_synchronized
-- name    : BalanceSpecification.fiveSymbol_mixing_biBalanced_not_synchronized
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T02:51:42.017858+00:00
-- url     : https://prove2.me/theorems/51f62f22-dab9-486a-bc80-6f7d398dd9fc
-- title:
--   Balance Specification: five Symbol mixing bi Balanced not synchronized
-- statement:
--   The exact five-symbol forbidden-word shift of the final source example is
--   irreducible, topologically mixing and bi-balanced, and has no synchronizing word.
--   Source: `eg::mixing_bi-balanced_not-synchronizing`, lines 742–793.
--
--   Source: https://github.com/pseudorandom/balance_and_specification/blob/62771ced95e6f431064d40780b623362263ae9e4/BalanceSpecificaton/Examples.lean#L17-L21
-- source:
--   https://github.com/pseudorandom/balance_and_specification/blob/62771ced95e6f431064d40780b623362263ae9e4/BalanceSpecificaton/Examples.lean#L17-L21

module
public import Definitions.Def_BalanceSpecificaton_FiveSymbolBalance
public import Definitions.Def_BalanceSpecificaton_TopologicalMixing
public import Definitions.Def_BalanceSpecificaton_OneSidedBounds
public import Definitions.Def_BalanceSpecificaton_Examples
set_option autoImplicit true
@[expose] public section
public section
open BalanceSpecification

theorem BalanceSpecification.fiveSymbol_mixing_biBalanced_not_synchronized :
    Irreducible FiveSymbol.shift ∧ TopologicallyMixing FiveSymbol.shift ∧
      BiBalanced (language FiveSymbol.shift) ∧ ¬Synchronized FiveSymbol.shift := by sorry
