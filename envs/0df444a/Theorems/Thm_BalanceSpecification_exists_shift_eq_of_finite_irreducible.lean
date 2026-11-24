-- Prove2me | Theorems.Thm_BalanceSpecification_exists_shift_eq_of_finite_irreducible
-- name    : BalanceSpecification.exists_shift_eq_of_finite_irreducible
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T01:54:15.766547+00:00
-- url     : https://prove2.me/theorems/49ac81ef-4afe-4850-813f-8643f3004fa3
-- title:
--   Balance Specification: exists shift eq of finite irreducible
-- statement:
--   On a finite irreducible shift, any point is a nonnegative translate of any other point.
--
--   Source: https://github.com/pseudorandom/balance_and_specification/blob/62771ced95e6f431064d40780b623362263ae9e4/BalanceSpecificaton/Periodicity.lean#L182-L222
-- source:
--   https://github.com/pseudorandom/balance_and_specification/blob/62771ced95e6f431064d40780b623362263ae9e4/BalanceSpecificaton/Periodicity.lean#L182-L222

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

theorem BalanceSpecification.exists_shift_eq_of_finite_irreducible (hfin : X.carrier.Finite)
    (hirr : Irreducible X) {x y : Configuration A}
    (hx : x ∈ X.carrier) (hy : y ∈ X.carrier) :
    ∃ n : ℕ, SymbolicDynamics.FullShift.shift (n : ℤ) x = y := by sorry
