-- Prove2me | Theorems.Thm_BalanceSpecification_mem_languageShift_iff_interiors
-- name    : BalanceSpecification.mem_languageShift_iff_interiors
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-24T02:08:25.559804+00:00
-- url     : https://prove2.me/theorems/3365f953-ea0c-4173-80d8-f4b92a795edc
-- title:
--   Balance Specification: mem language Shift iff interiors
-- statement:
--   The associated language is exactly the intersection of all admissible interiors.
--
--   Source: https://github.com/pseudorandom/balance_and_specification/blob/62771ced95e6f431064d40780b623362263ae9e4/BalanceSpecificaton/FactorialEntropy.lean#L167-L172
-- source:
--   https://github.com/pseudorandom/balance_and_specification/blob/62771ced95e6f431064d40780b623362263ae9e4/BalanceSpecificaton/FactorialEntropy.lean#L167-L172

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

theorem BalanceSpecification.mem_languageShift_iff_interiors [Nonempty A]
    {L : Set (Word A)} (hL : IsFactorial L) {w : Word A} :
    w ∈ language (languageShift L) ↔ ∀ M, w ∈ interiorLanguage L M := by sorry
