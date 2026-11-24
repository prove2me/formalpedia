-- Prove2me | Theorems.Thm_BalanceSpecification_languageEntropy_eq_languageShift
-- name    : BalanceSpecification.languageEntropy_eq_languageShift
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-24T01:48:38.138578+00:00
-- url     : https://prove2.me/theorems/39a02f4f-e8e1-44aa-9428-48c640393bb8
-- title:
--   Balance Specification: language Entropy eq language Shift
-- statement:
--   The source's factorial-language entropy theorem, including the empty shift
--   and minus-infinity entropy cases.
--
--   Source: https://github.com/pseudorandom/balance_and_specification/blob/62771ced95e6f431064d40780b623362263ae9e4/BalanceSpecificaton/FactorialEntropy.lean#L349-L378
-- source:
--   https://github.com/pseudorandom/balance_and_specification/blob/62771ced95e6f431064d40780b623362263ae9e4/BalanceSpecificaton/FactorialEntropy.lean#L349-L378

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

theorem BalanceSpecification.languageEntropy_eq_languageShift {L : Set (Word A)} (hL : IsFactorial L) :
    languageEntropy L = languageEntropy (language (languageShift L)) := by sorry
