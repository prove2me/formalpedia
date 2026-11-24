-- Prove2me | Theorems.Thm_BalanceSpecification_interiorLanguage_subset
-- name    : BalanceSpecification.interiorLanguage_subset
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T02:28:19.607801+00:00
-- url     : https://prove2.me/theorems/06b4c130-6c61-471a-b124-c6d2404db8a3
-- title:
--   Balance Specification: interior Language subset
-- statement:
--   The Balance Specification construction uses the interior Language subset property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/pseudorandom/balance_and_specification/blob/62771ced95e6f431064d40780b623362263ae9e4/BalanceSpecificaton/TilingBounds.lean#L38-L41
-- source:
--   https://github.com/pseudorandom/balance_and_specification/blob/62771ced95e6f431064d40780b623362263ae9e4/BalanceSpecificaton/TilingBounds.lean#L38-L41

module
public import Definitions.Def_BalanceSpecificaton_CountBounds
public import Mathlib.Data.Fintype.Prod
public import Mathlib.Tactic
public import Definitions.Def_BalanceSpecificaton_TilingBounds
set_option autoImplicit true
@[expose] public section
public section
noncomputable section
open BalanceSpecification
variable {A : Type*}

theorem BalanceSpecification.interiorLanguage_subset {L : Set (Word A)} (hL : IsFactorial L) (M : ℕ) :
    interiorLanguage L M ⊆ L := by sorry
