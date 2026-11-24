-- Prove2me | Theorems.Thm_BalanceSpecification_codedShift_irreducible
-- name    : BalanceSpecification.codedShift_irreducible
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T01:43:13.013044+00:00
-- url     : https://prove2.me/theorems/2ab7b268-a944-416f-a98c-960c82f523ab
-- title:
--   Balance Specification: coded Shift irreducible
-- statement:
--   Coded shifts are irreducible: concatenate finite generator words containing
--   the prescribed two words, then retain the intervening subword as a bridge.
--
--   Source: https://github.com/pseudorandom/balance_and_specification/blob/62771ced95e6f431064d40780b623362263ae9e4/BalanceSpecificaton/CodedLanguage.lean#L289-L305
-- source:
--   https://github.com/pseudorandom/balance_and_specification/blob/62771ced95e6f431064d40780b623362263ae9e4/BalanceSpecificaton/CodedLanguage.lean#L289-L305

module
public import Definitions.Def_BalanceSpecificaton_Coded
public import Definitions.Def_BalanceSpecificaton_Forbidden
public import Mathlib.Tactic
public import Definitions.Def_BalanceSpecificaton_CodedLanguage
set_option autoImplicit true
@[expose] public section
public section
open BalanceSpecification
variable {A : Type*}

theorem BalanceSpecification.codedShift_irreducible [TopologicalSpace A] [DiscreteTopology A]
    (C : Set (Word A)) : Irreducible (codedShift C) := by sorry
