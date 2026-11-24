-- Prove2me | Theorems.Thm_BalanceSpecification_languageEntropy_eq_entropy_languageShift
-- name    : BalanceSpecification.languageEntropy_eq_entropy_languageShift
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-24T02:40:39.960486+00:00
-- url     : https://prove2.me/theorems/88c5a5f9-d413-4d45-8232-e41e436948de
-- title:
--   Balance Specification: language Entropy eq entropy language Shift
-- statement:
--   The real-entropy formulation when the associated shift is nonempty.
--
--   Source: https://github.com/pseudorandom/balance_and_specification/blob/62771ced95e6f431064d40780b623362263ae9e4/BalanceSpecificaton/FactorialEntropy.lean#L381-L384
-- source:
--   https://github.com/pseudorandom/balance_and_specification/blob/62771ced95e6f431064d40780b623362263ae9e4/BalanceSpecificaton/FactorialEntropy.lean#L381-L384

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

theorem BalanceSpecification.languageEntropy_eq_entropy_languageShift {L : Set (Word A)}
    (hL : IsFactorial L) (hX : (languageShift L).carrier.Nonempty) :
    languageEntropy L = (entropy (languageShift L) hX : EReal) := by sorry
