-- Prove2me | Theorems.Thm_BalanceSpecification_finite_carrier_of_bounded_wordCount
-- name    : BalanceSpecification.finite_carrier_of_bounded_wordCount
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T01:45:09.875501+00:00
-- url     : https://prove2.me/theorems/8236a326-eed9-4062-b6ab-a8e8c28cab71
-- title:
--   Balance Specification: finite carrier of bounded word Count
-- statement:
--   A uniform finite bound on word counts forces the shift itself to be finite.
--
--   Source: https://github.com/pseudorandom/balance_and_specification/blob/62771ced95e6f431064d40780b623362263ae9e4/BalanceSpecificaton/Periodicity.lean#L63-L76
-- source:
--   https://github.com/pseudorandom/balance_and_specification/blob/62771ced95e6f431064d40780b623362263ae9e4/BalanceSpecificaton/Periodicity.lean#L63-L76

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

theorem BalanceSpecification.finite_carrier_of_bounded_wordCount
    (h : ∃ C : ℕ, ∀ n, wordCount (language X) n ≤ C) : X.carrier.Finite := by sorry
