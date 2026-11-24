-- Prove2me | Theorems.Thm_BalanceSpecification_shiftMap_iterate_val
-- name    : BalanceSpecification.shiftMap_iterate_val
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T01:33:11.603386+00:00
-- url     : https://prove2.me/theorems/67e7335e-4278-4436-9f6b-463cff8aaa4e
-- title:
--   Balance Specification: shift Map iterate val
-- statement:
--   The Balance Specification construction uses the shift Map iterate val property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/pseudorandom/balance_and_specification/blob/62771ced95e6f431064d40780b623362263ae9e4/BalanceSpecificaton/Periodicity.lean#L140-L153
-- source:
--   https://github.com/pseudorandom/balance_and_specification/blob/62771ced95e6f431064d40780b623362263ae9e4/BalanceSpecificaton/Periodicity.lean#L140-L153

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

theorem BalanceSpecification.shiftMap_iterate_val (X : ShiftSpace A) (x : X.carrier) (n : ℕ) :
    ((shiftMap X)^[n] x).val = SymbolicDynamics.FullShift.shift (n : ℤ) x.val := by sorry
