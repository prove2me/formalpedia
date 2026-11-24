-- Prove2me | Theorems.Thm_BalanceSpecification_bsm_iff_finite_periodic_carrier_of_entropy_zero
-- name    : BalanceSpecification.bsm_iff_finite_periodic_carrier_of_entropy_zero
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-24T01:54:05.572058+00:00
-- url     : https://prove2.me/theorems/e579a06c-6b9b-4a76-b376-9aa7fea40d58
-- title:
--   Balance Specification: bsm iff finite periodic carrier of entropy zero
-- statement:
--   The zero-entropy BSM characterization includes the periodicity of every point.
--
--   Source: https://github.com/pseudorandom/balance_and_specification/blob/62771ced95e6f431064d40780b623362263ae9e4/BalanceSpecificaton/Periodicity.lean#L168-L178
-- source:
--   https://github.com/pseudorandom/balance_and_specification/blob/62771ced95e6f431064d40780b623362263ae9e4/BalanceSpecificaton/Periodicity.lean#L168-L178

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

theorem BalanceSpecification.bsm_iff_finite_periodic_carrier_of_entropy_zero (hX : X.carrier.Nonempty)
    (hh : entropy X hX = 0) :
    BoundedlySupermultiplicative (language X) ↔
      X.carrier.Finite ∧ ∀ x ∈ X.carrier,
        ∃ p : ℕ, 0 < p ∧ SymbolicDynamics.FullShift.shift (p : ℤ) x = x := by sorry
