-- Prove2me | Theorems.Thm_BalanceSpecification_bsm_zero_entropy_characterization
-- name    : BalanceSpecification.bsm_zero_entropy_characterization
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T02:53:02.338807+00:00
-- url     : https://prove2.me/theorems/b35eb082-9ecf-4dab-a730-861e1f7c2121
-- title:
--   Balance Specification: bsm zero entropy characterization
-- statement:
--   Both sentences of `prop::BSM_zero_entropy_condition`, source lines 175–178.
--   The two characterizations share the same nonempty zero-entropy shift.
--
--   Source: https://github.com/pseudorandom/balance_and_specification/blob/62771ced95e6f431064d40780b623362263ae9e4/BalanceSpecificaton/Results.lean#L19-L29
-- source:
--   https://github.com/pseudorandom/balance_and_specification/blob/62771ced95e6f431064d40780b623362263ae9e4/BalanceSpecificaton/Results.lean#L19-L29

module
public import Definitions.Def_BalanceSpecificaton_Periodicity
public import Definitions.Def_BalanceSpecificaton_Synchronization
public import Definitions.Def_BalanceSpecificaton_Specification
public import Definitions.Def_BalanceSpecificaton_Results
set_option autoImplicit true
@[expose] public section
public section
open BalanceSpecification
variable {A : Type*} [Fintype A] [TopologicalSpace A] {X : ShiftSpace A}

theorem BalanceSpecification.bsm_zero_entropy_characterization (hX : X.carrier.Nonempty)
    (hh : entropy X hX = 0) :
    (BoundedlySupermultiplicative (language X) ↔
      X.carrier.Finite ∧ ∀ x ∈ X.carrier,
        ∃ p : ℕ, 0 < p ∧ SymbolicDynamics.FullShift.shift (p : ℤ) x = x) ∧
    ((Irreducible X ∧ BoundedlySupermultiplicative (language X)) ↔
      ∃ x ∈ X.carrier,
        (∃ p : ℕ, 0 < p ∧ SymbolicDynamics.FullShift.shift (p : ℤ) x = x) ∧
        X.carrier = {y | ∃ n : ℕ, SymbolicDynamics.FullShift.shift (n : ℤ) x = y}) := by sorry
