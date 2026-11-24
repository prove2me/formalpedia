-- Prove2me | Theorems.Thm_BalanceSpecification_block_periodicConfiguration
-- name    : BalanceSpecification.block_periodicConfiguration
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T01:42:53.664857+00:00
-- url     : https://prove2.me/theorems/b98c7e37-d1f8-47a7-aede-5e66eb38d0ff
-- title:
--   Balance Specification: block periodic Configuration
-- statement:
--   A complete generator word is read between each two consecutive periodic cuts.
--
--   Source: https://github.com/pseudorandom/balance_and_specification/blob/62771ced95e6f431064d40780b623362263ae9e4/BalanceSpecificaton/Coded.lean#L100-L109
-- source:
--   https://github.com/pseudorandom/balance_and_specification/blob/62771ced95e6f431064d40780b623362263ae9e4/BalanceSpecificaton/Coded.lean#L100-L109

module
public import Definitions.Def_BalanceSpecificaton_LanguageProperties
public import Mathlib.Topology.Continuous
public import Mathlib.Tactic
public import Definitions.Def_BalanceSpecificaton_Coded
set_option autoImplicit true
@[expose] public section
public section
open BalanceSpecification
variable {A : Type*}

theorem BalanceSpecification.block_periodicConfiguration (w : Word A) (hw : 0 < w.length) (j : ℤ) :
    block (periodicConfiguration w hw) (j * w.length) w.length = w := by sorry
