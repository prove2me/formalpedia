-- Prove2me | Theorems.Thm_BalanceSpecification_languageEntropy_language_eq_entropy
-- name    : BalanceSpecification.languageEntropy_language_eq_entropy
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T01:43:45.282386+00:00
-- url     : https://prove2.me/theorems/75f0d5a9-39a7-4eea-b0b6-d7a5dfb6396f
-- title:
--   Balance Specification: language Entropy language eq entropy
-- statement:
--   For a nonempty shift, the extended language entropy is its real word-growth entropy.
--
--   Source: https://github.com/pseudorandom/balance_and_specification/blob/62771ced95e6f431064d40780b623362263ae9e4/BalanceSpecificaton/FactorialEntropy.lean#L301-L303
-- source:
--   https://github.com/pseudorandom/balance_and_specification/blob/62771ced95e6f431064d40780b623362263ae9e4/BalanceSpecificaton/FactorialEntropy.lean#L301-L303

module
public import Definitions.Def_BalanceSpecificaton_Forbidden
public import Definitions.Def_BalanceSpecificaton_Counting
public import Definitions.Def_BalanceSpecificaton_TilingBounds
public import Definitions.Def_BalanceSpecificaton_Entropy
public import Definitions.Def_BalanceSpecificaton_GrowthTiling
public import Mathlib.Analysis.SpecialFunctions.Log.ENNRealLog
public import Mathlib.Topology.Instances.EReal.Lemmas
public import Mathlib.Topology.Compactness.Compact
public import Mathlib.Tactic
public import Definitions.Def_BalanceSpecificaton_FactorialEntropy
set_option autoImplicit true
@[expose] public section
public section
noncomputable section
open scoped ENNReal
open BalanceSpecification
variable {A : Type*}
variable [TopologicalSpace A] [DiscreteTopology A]
variable [Fintype A]
omit [DiscreteTopology A]

theorem BalanceSpecification.languageEntropy_language_eq_entropy {X : ShiftSpace A}
    (hX : X.carrier.Nonempty) : languageEntropy (language X) = (entropy X hX : EReal) := by sorry
