-- Prove2me | Theorems.Thm_BalanceSpecification_mem_interiors_of_mem_languageShift
-- name    : BalanceSpecification.mem_interiors_of_mem_languageShift
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-24T02:08:23.757818+00:00
-- url     : https://prove2.me/theorems/549b0b40-d93b-4b47-9c54-9714e0a278cb
-- title:
--   Balance Specification: mem interiors of mem language Shift
-- statement:
--   Every word of the associated shift has arbitrarily much admissible context.
--
--   Source: https://github.com/pseudorandom/balance_and_specification/blob/62771ced95e6f431064d40780b623362263ae9e4/BalanceSpecificaton/FactorialEntropy.lean#L153-L164
-- source:
--   https://github.com/pseudorandom/balance_and_specification/blob/62771ced95e6f431064d40780b623362263ae9e4/BalanceSpecificaton/FactorialEntropy.lean#L153-L164

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
omit [Fintype A]

theorem BalanceSpecification.mem_interiors_of_mem_languageShift {L : Set (Word A)} {w : Word A}
    (hw : w ∈ language (languageShift L)) (M : ℕ) : w ∈ interiorLanguage L M := by sorry
