-- Prove2me | Theorems.Thm_BalanceSpecification_wordCount_le_ncard_of_finite_carrier
-- name    : BalanceSpecification.wordCount_le_ncard_of_finite_carrier
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T01:54:01.394806+00:00
-- url     : https://prove2.me/theorems/2130a314-1a80-4bad-b7cc-c3a0fe0f7c3f
-- title:
--   Balance Specification: word Count le ncard of finite carrier
-- statement:
--   Every word can be read at the origin, so finite shifts have bounded word counts.
--
--   Source: https://github.com/pseudorandom/balance_and_specification/blob/62771ced95e6f431064d40780b623362263ae9e4/BalanceSpecificaton/Periodicity.lean#L79-L96
-- source:
--   https://github.com/pseudorandom/balance_and_specification/blob/62771ced95e6f431064d40780b623362263ae9e4/BalanceSpecificaton/Periodicity.lean#L79-L96

module
public import Definitions.Def_BalanceSpecificaton_Entropy
public import Definitions.Def_BalanceSpecificaton_LanguageProperties
public import Definitions.Def_BalanceSpecificaton_Specification
public import Mathlib.Data.Set.Card
public import Mathlib.Dynamics.PeriodicPts.Lemmas
public import Mathlib.Tactic
public import Definitions.Def_BalanceSpecificaton_Periodicity
set_option autoImplicit true
@[expose] public section
public section
noncomputable section
open BalanceSpecification
variable {A : Type*}
variable [Fintype A] [TopologicalSpace A] {X : ShiftSpace A}

theorem BalanceSpecification.wordCount_le_ncard_of_finite_carrier (hX : X.carrier.Finite) (n : ℕ) :
    wordCount (language X) n ≤ X.carrier.ncard := by sorry
