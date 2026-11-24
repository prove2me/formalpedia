-- Prove2me | Theorems.Thm_BalanceSpecification_carrier_subset_of_language_subset
-- name    : BalanceSpecification.carrier_subset_of_language_subset
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T01:33:46.504122+00:00
-- url     : https://prove2.me/theorems/f77e2639-bb82-40eb-8f6d-4299dd981ae6
-- title:
--   Balance Specification: carrier subset of language subset
-- statement:
--   Inclusion of languages implies inclusion of their closed shift spaces.
--
--   Source: https://github.com/pseudorandom/balance_and_specification/blob/62771ced95e6f431064d40780b623362263ae9e4/BalanceSpecificaton/LanguageProperties.lean#L126-L131
-- source:
--   https://github.com/pseudorandom/balance_and_specification/blob/62771ced95e6f431064d40780b623362263ae9e4/BalanceSpecificaton/LanguageProperties.lean#L126-L131

module
public import Definitions.Def_BalanceSpecificaton_Language
public import Mathlib.Tactic
public import Definitions.Def_BalanceSpecificaton_LanguageProperties
set_option autoImplicit true
@[expose] public section
public section
open BalanceSpecification
variable {A : Type*}
variable [TopologicalSpace A] {X : ShiftSpace A}

theorem BalanceSpecification.carrier_subset_of_language_subset {Y : ShiftSpace A}
    (h : language X ⊆ language Y) : X.carrier ⊆ Y.carrier := by sorry
