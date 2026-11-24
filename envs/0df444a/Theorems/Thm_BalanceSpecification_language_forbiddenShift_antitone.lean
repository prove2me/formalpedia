-- Prove2me | Theorems.Thm_BalanceSpecification_language_forbiddenShift_antitone
-- name    : BalanceSpecification.language_forbiddenShift_antitone
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-24T02:19:25.876809+00:00
-- url     : https://prove2.me/theorems/66164987-d82e-458f-a109-2d2fe592c58c
-- title:
--   Balance Specification: language forbidden Shift antitone
-- statement:
--   The Balance Specification construction uses the language forbidden Shift antitone property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/pseudorandom/balance_and_specification/blob/62771ced95e6f431064d40780b623362263ae9e4/BalanceSpecificaton/Forbidden.lean#L114-L117
-- source:
--   https://github.com/pseudorandom/balance_and_specification/blob/62771ced95e6f431064d40780b623362263ae9e4/BalanceSpecificaton/Forbidden.lean#L114-L117

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

theorem BalanceSpecification.language_forbiddenShift_antitone {F G : Set (Word A)} (hFG : F ⊆ G) :
    language (forbiddenShift G) ⊆ language (forbiddenShift F) := by sorry
