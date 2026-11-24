-- Prove2me | Theorems.Thm_BalanceSpecification_zero_entropy_balanced_specification_equivalences
-- name    : BalanceSpecification.zero_entropy_balanced_specification_equivalences
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T02:19:06.379918+00:00
-- url     : https://prove2.me/theorems/db0787b5-6e3d-4e0a-b0a0-f6a5697137a6
-- title:
--   Balance Specification: zero entropy balanced specification equivalences
-- statement:
--   The four equivalent properties stated immediately after the zero-entropy proposition.
--
--   Source: https://github.com/pseudorandom/balance_and_specification/blob/62771ced95e6f431064d40780b623362263ae9e4/BalanceSpecificaton/Periodicity.lean#L411-L431
-- source:
--   https://github.com/pseudorandom/balance_and_specification/blob/62771ced95e6f431064d40780b623362263ae9e4/BalanceSpecificaton/Periodicity.lean#L411-L431

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

theorem BalanceSpecification.zero_entropy_balanced_specification_equivalences (hX : X.carrier.Nonempty)
    (hh : entropy X hX = 0) (hirr : Irreducible X) :
    (HasVariableSpecification X ↔ BiBalanced (language X)) ∧
    (BiBalanced (language X) ↔ RightBalanced (language X) ∨ LeftBalanced (language X)) ∧
    ((RightBalanced (language X) ∨ LeftBalanced (language X)) ↔
      BoundedlySupermultiplicative (language X)) := by sorry
