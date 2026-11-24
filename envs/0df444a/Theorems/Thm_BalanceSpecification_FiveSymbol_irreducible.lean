-- Prove2me | Theorems.Thm_BalanceSpecification_FiveSymbol_irreducible
-- name    : BalanceSpecification.FiveSymbol.irreducible
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-24T01:52:17.604876+00:00
-- url     : https://prove2.me/theorems/7dddc587-94d3-434c-8d42-d1675d4e1407
-- title:
--   Five Symbol: irreducible
-- statement:
--   In particular, the source's standing irreducibility assumption holds.
--
--   Source: https://github.com/pseudorandom/balance_and_specification/blob/62771ced95e6f431064d40780b623362263ae9e4/BalanceSpecificaton/FiveSymbol.lean#L574-L578
-- source:
--   https://github.com/pseudorandom/balance_and_specification/blob/62771ced95e6f431064d40780b623362263ae9e4/BalanceSpecificaton/FiveSymbol.lean#L574-L578

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

theorem BalanceSpecification.FiveSymbol.irreducible : Irreducible shift := by sorry
