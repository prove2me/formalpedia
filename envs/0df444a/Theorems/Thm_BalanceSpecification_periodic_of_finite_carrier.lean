-- Prove2me | Theorems.Thm_BalanceSpecification_periodic_of_finite_carrier
-- name    : BalanceSpecification.periodic_of_finite_carrier
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T01:45:10.492805+00:00
-- url     : https://prove2.me/theorems/0d6a507f-9021-4815-a7cd-cb316f58352e
-- title:
--   Balance Specification: periodic of finite carrier
-- statement:
--   Every configuration in a finite shift space is periodic.
--
--   Source: https://github.com/pseudorandom/balance_and_specification/blob/62771ced95e6f431064d40780b623362263ae9e4/BalanceSpecificaton/Periodicity.lean#L157-L165
-- source:
--   https://github.com/pseudorandom/balance_and_specification/blob/62771ced95e6f431064d40780b623362263ae9e4/BalanceSpecificaton/Periodicity.lean#L157-L165

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

theorem BalanceSpecification.periodic_of_finite_carrier (hX : X.carrier.Finite) {x : Configuration A}
    (hx : x ∈ X.carrier) :
    ∃ p : ℕ, 0 < p ∧ SymbolicDynamics.FullShift.shift (p : ℤ) x = x := by sorry
