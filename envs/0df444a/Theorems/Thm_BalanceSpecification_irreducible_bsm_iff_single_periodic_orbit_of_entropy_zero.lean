-- Prove2me | Theorems.Thm_BalanceSpecification_irreducible_bsm_iff_single_periodic_orbit_of_entropy_zero
-- name    : BalanceSpecification.irreducible_bsm_iff_single_periodic_orbit_of_entropy_zero
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-24T01:54:32.099785+00:00
-- url     : https://prove2.me/theorems/ab75c746-ca2b-4aae-a31a-b3e804b1a7d6
-- title:
--   Balance Specification: irreducible bsm iff single periodic orbit of entropy zero
-- statement:
--   The irreducible clause of the zero-entropy BSM proposition.
--
--   Source: https://github.com/pseudorandom/balance_and_specification/blob/62771ced95e6f431064d40780b623362263ae9e4/BalanceSpecificaton/Periodicity.lean#L308-L321
-- source:
--   https://github.com/pseudorandom/balance_and_specification/blob/62771ced95e6f431064d40780b623362263ae9e4/BalanceSpecificaton/Periodicity.lean#L308-L321

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

theorem BalanceSpecification.irreducible_bsm_iff_single_periodic_orbit_of_entropy_zero
    (hX : X.carrier.Nonempty) (hh : entropy X hX = 0) :
    (Irreducible X ∧ BoundedlySupermultiplicative (language X)) ↔
      ∃ x ∈ X.carrier,
        (∃ p : ℕ, 0 < p ∧ SymbolicDynamics.FullShift.shift (p : ℤ) x = x) ∧
        X.carrier = {y | ∃ n : ℕ, SymbolicDynamics.FullShift.shift (n : ℤ) x = y} := by sorry
