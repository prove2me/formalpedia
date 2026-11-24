-- Prove2me | Theorems.Thm_BalanceSpecification_finite_carrier_iff_bounded_wordCount
-- name    : BalanceSpecification.finite_carrier_iff_bounded_wordCount
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T01:54:01.093278+00:00
-- url     : https://prove2.me/theorems/c289e57c-6faf-44f1-ac7f-50cfd9ba9d75
-- title:
--   Balance Specification: finite carrier iff bounded word Count
-- statement:
--   A shift is finite exactly when its finite-word complexity is uniformly bounded.
--
--   Source: https://github.com/pseudorandom/balance_and_specification/blob/62771ced95e6f431064d40780b623362263ae9e4/BalanceSpecificaton/Periodicity.lean#L99-L104
-- source:
--   https://github.com/pseudorandom/balance_and_specification/blob/62771ced95e6f431064d40780b623362263ae9e4/BalanceSpecificaton/Periodicity.lean#L99-L104

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

theorem BalanceSpecification.finite_carrier_iff_bounded_wordCount : X.carrier.Finite ↔
    ∃ C : ℕ, ∀ n, wordCount (language X) n ≤ C := by sorry
