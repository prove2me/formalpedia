-- Prove2me | Theorems.Thm_BalanceSpecification_OneSidedExample_unequal_mem_code
-- name    : BalanceSpecification.OneSidedExample.unequal_mem_code
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T02:12:27.392739+00:00
-- url     : https://prove2.me/theorems/7559f8ec-28fe-4d71-8ed8-cfec760902f2
-- title:
--   One Sided Example: unequal mem code
-- statement:
--   The One Sided Example construction uses the unequal mem code property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/pseudorandom/balance_and_specification/blob/62771ced95e6f431064d40780b623362263ae9e4/BalanceSpecificaton/OneSidedExample.lean#L44-L46
-- source:
--   https://github.com/pseudorandom/balance_and_specification/blob/62771ced95e6f431064d40780b623362263ae9e4/BalanceSpecificaton/OneSidedExample.lean#L44-L46

module
public import Definitions.Def_BalanceSpecificaton_CodedLanguage
public import Definitions.Def_BalanceSpecificaton_Specification
public import Mathlib.Tactic
public import Definitions.Def_BalanceSpecificaton_OneSidedExample
set_option autoImplicit true
@[expose] public section
public section
open BalanceSpecification BalanceSpecification.OneSidedExample

theorem BalanceSpecification.OneSidedExample.unequal_mem_code {l m : ℕ} (hm : 1 ≤ m) (hlm : m < l) :
    List.replicate l a ++ List.replicate m b ++ [c] ∈ code := by sorry
