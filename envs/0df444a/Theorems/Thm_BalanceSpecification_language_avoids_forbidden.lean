-- Prove2me | Theorems.Thm_BalanceSpecification_language_avoids_forbidden
-- name    : BalanceSpecification.language_avoids_forbidden
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T01:54:53.484534+00:00
-- url     : https://prove2.me/theorems/a3725cea-ea82-47c3-bf03-636b47849b41
-- title:
--   Balance Specification: language avoids forbidden
-- statement:
--   An admissible word contains no forbidden word as a contiguous subword.
--
--   Source: https://github.com/pseudorandom/balance_and_specification/blob/62771ced95e6f431064d40780b623362263ae9e4/BalanceSpecificaton/Forbidden.lean#L103-L106
-- source:
--   https://github.com/pseudorandom/balance_and_specification/blob/62771ced95e6f431064d40780b623362263ae9e4/BalanceSpecificaton/Forbidden.lean#L103-L106

module
public import Definitions.Def_BalanceSpecificaton_LanguageProperties
public import Mathlib.Tactic
public import Definitions.Def_BalanceSpecificaton_Forbidden
set_option autoImplicit true
@[expose] public section
public section
open BalanceSpecification
variable {A : Type*}
variable [TopologicalSpace A] [DiscreteTopology A]

theorem BalanceSpecification.language_avoids_forbidden {F : Set (Word A)} {u : Word A}
    (hu : u ∈ language (forbiddenShift F)) : ∀ w ∈ F, ¬ w <:+: u := by sorry
