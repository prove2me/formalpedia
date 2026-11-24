-- Prove2me | Theorems.Thm_BalanceSpecification_hasVariableSpecification_of_single_periodic_orbit
-- name    : BalanceSpecification.hasVariableSpecification_of_single_periodic_orbit
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T01:54:32.976236+00:00
-- url     : https://prove2.me/theorems/c7546ecc-4323-492f-b514-9760175a8b1d
-- title:
--   Balance Specification: has Variable Specification of single periodic orbit
-- statement:
--   A single periodic orbit has a uniform variable-specification bound.
--
--   Source: https://github.com/pseudorandom/balance_and_specification/blob/62771ced95e6f431064d40780b623362263ae9e4/BalanceSpecificaton/Periodicity.lean#L325-L390
-- source:
--   https://github.com/pseudorandom/balance_and_specification/blob/62771ced95e6f431064d40780b623362263ae9e4/BalanceSpecificaton/Periodicity.lean#L325-L390

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

theorem BalanceSpecification.hasVariableSpecification_of_single_periodic_orbit {x : Configuration A}
    (hx : x ∈ X.carrier) {p : ℕ} (hp : 0 < p)
    (hperiod : SymbolicDynamics.FullShift.shift (p : ℤ) x = x)
    (horbit : X.carrier = {y | ∃ n : ℕ,
      SymbolicDynamics.FullShift.shift (n : ℤ) x = y}) : HasVariableSpecification X := by sorry
