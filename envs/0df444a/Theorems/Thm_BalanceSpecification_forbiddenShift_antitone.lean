-- Prove2me | Theorems.Thm_BalanceSpecification_forbiddenShift_antitone
-- name    : BalanceSpecification.forbiddenShift_antitone
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T01:54:55.520798+00:00
-- url     : https://prove2.me/theorems/da29daed-bcbd-4a77-b835-9dddba2f4287
-- title:
--   Balance Specification: forbidden Shift antitone
-- statement:
--   Adding forbidden words can only shrink the shift.
--
--   Source: https://github.com/pseudorandom/balance_and_specification/blob/62771ced95e6f431064d40780b623362263ae9e4/BalanceSpecificaton/Forbidden.lean#L109-L112
-- source:
--   https://github.com/pseudorandom/balance_and_specification/blob/62771ced95e6f431064d40780b623362263ae9e4/BalanceSpecificaton/Forbidden.lean#L109-L112

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

theorem BalanceSpecification.forbiddenShift_antitone {F G : Set (Word A)} (hFG : F ⊆ G) :
    (forbiddenShift G).carrier ⊆ (forbiddenShift F).carrier := by sorry
