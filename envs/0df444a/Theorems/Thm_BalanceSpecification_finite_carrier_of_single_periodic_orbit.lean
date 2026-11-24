-- Prove2me | Theorems.Thm_BalanceSpecification_finite_carrier_of_single_periodic_orbit
-- name    : BalanceSpecification.finite_carrier_of_single_periodic_orbit
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T01:54:16.682259+00:00
-- url     : https://prove2.me/theorems/24eb4052-203b-43e8-a916-cd9e5c823f6b
-- title:
--   Balance Specification: finite carrier of single periodic orbit
-- statement:
--   One periodic orbit is a finite set of configurations.
--
--   Source: https://github.com/pseudorandom/balance_and_specification/blob/62771ced95e6f431064d40780b623362263ae9e4/BalanceSpecificaton/Periodicity.lean#L242-L256
-- source:
--   https://github.com/pseudorandom/balance_and_specification/blob/62771ced95e6f431064d40780b623362263ae9e4/BalanceSpecificaton/Periodicity.lean#L242-L256

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
omit [Fintype A]

theorem BalanceSpecification.finite_carrier_of_single_periodic_orbit {x : Configuration A}
    (hx : x ∈ X.carrier) {p : ℕ} (hp : 0 < p)
    (hperiod : SymbolicDynamics.FullShift.shift (p : ℤ) x = x)
    (horbit : X.carrier = {y | ∃ n : ℕ,
      SymbolicDynamics.FullShift.shift (n : ℤ) x = y}) : X.carrier.Finite := by sorry
