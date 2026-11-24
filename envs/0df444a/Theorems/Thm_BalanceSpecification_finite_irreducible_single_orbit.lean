-- Prove2me | Theorems.Thm_BalanceSpecification_finite_irreducible_single_orbit
-- name    : BalanceSpecification.finite_irreducible_single_orbit
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T01:45:14.83086+00:00
-- url     : https://prove2.me/theorems/a9aa3f90-451b-4652-957f-fcb0b0f25cdc
-- title:
--   Balance Specification: finite irreducible single orbit
-- statement:
--   A finite nonempty irreducible shift consists of one periodic orbit.
--
--   Source: https://github.com/pseudorandom/balance_and_specification/blob/62771ced95e6f431064d40780b623362263ae9e4/BalanceSpecificaton/Periodicity.lean#L226-L238
-- source:
--   https://github.com/pseudorandom/balance_and_specification/blob/62771ced95e6f431064d40780b623362263ae9e4/BalanceSpecificaton/Periodicity.lean#L226-L238

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

theorem BalanceSpecification.finite_irreducible_single_orbit (hfin : X.carrier.Finite)
    (hX : X.carrier.Nonempty) (hirr : Irreducible X) :
    ∃ x ∈ X.carrier,
      (∃ p : ℕ, 0 < p ∧ SymbolicDynamics.FullShift.shift (p : ℤ) x = x) ∧
      X.carrier = {y | ∃ n : ℕ, SymbolicDynamics.FullShift.shift (n : ℤ) x = y} := by sorry
