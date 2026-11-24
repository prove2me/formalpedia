-- Prove2me | Theorems.Thm_BalanceSpecification_exists_oneSided_marker_extension
-- name    : BalanceSpecification.exists_oneSided_marker_extension
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-24T02:04:42.70917+00:00
-- url     : https://prove2.me/theorems/d9009fa1-44cd-4e5e-98b6-5625b5765df3
-- title:
--   Balance Specification: exists one Sided marker extension
-- statement:
--   The source's marker construction preserves the positive entropy of any
--   actual specification subsystem. No code-pressure, suffix-count, growth, or
--   balancedness estimate is assumed: all are produced from the source premises.
--
--   Source: https://github.com/pseudorandom/balance_and_specification/blob/62771ced95e6f431064d40780b623362263ae9e4/BalanceSpecificaton/MarkerConstruction.lean#L27-L96
-- source:
--   https://github.com/pseudorandom/balance_and_specification/blob/62771ced95e6f431064d40780b623362263ae9e4/BalanceSpecificaton/MarkerConstruction.lean#L27-L96

module
public import Definitions.Def_BalanceSpecificaton_MarkerWordBounds
public import Definitions.Def_BalanceSpecificaton_MarkerCodeCounts
public import Definitions.Def_BalanceSpecificaton_MarkedRenewal
public import Definitions.Def_BalanceSpecificaton_MarkerRight
public import Definitions.Def_BalanceSpecificaton_MarkerNonleft
public import Definitions.Def_BalanceSpecificaton_Specification
public import Definitions.Def_BalanceSpecificaton_MarkerConstruction
set_option autoImplicit true
@[expose] public section
public section
noncomputable section
open BalanceSpecification
open MarkerExtension
variable {A : Type*} [Fintype A] [TopologicalSpace A] [DiscreteTopology A]
  [TopologicalSpace (Option A)] [DiscreteTopology (Option A)] {Y : ShiftSpace A}

theorem BalanceSpecification.exists_oneSided_marker_extension (hY : Y.carrier.Nonempty)
    (hSpec : HasSpecification Y) (hentropy : 0 < entropy Y hY) :
    ∃ X : ShiftSpace (Option A), ∃ hX : X.carrier.Nonempty,
      IsCoded X ∧ Irreducible X ∧ entropy X hX = entropy Y hY ∧
      RightBalanced (language X) ∧ ¬LeftBalanced (language X) ∧
      ¬HasVariableSpecification X ∧
      (MarkerEmbedding.renamedShift (some : A → Option A) Y).carrier ⊆ X.carrier := by sorry
