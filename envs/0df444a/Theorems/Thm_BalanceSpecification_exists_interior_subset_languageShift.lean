-- Prove2me | Theorems.Thm_BalanceSpecification_exists_interior_subset_languageShift
-- name    : BalanceSpecification.exists_interior_subset_languageShift
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T02:08:29.171108+00:00
-- url     : https://prove2.me/theorems/976cb433-273e-4e75-89fc-05e9d295d93a
-- title:
--   Balance Specification: exists interior subset language Shift
-- statement:
--   At any fixed word length, sufficiently deep interiors already lie in the
--   associated shift's language. The depth is independent of the word.
--
--   Source: https://github.com/pseudorandom/balance_and_specification/blob/62771ced95e6f431064d40780b623362263ae9e4/BalanceSpecificaton/FactorialEntropy.lean#L176-L194
-- source:
--   https://github.com/pseudorandom/balance_and_specification/blob/62771ced95e6f431064d40780b623362263ae9e4/BalanceSpecificaton/FactorialEntropy.lean#L176-L194

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

theorem BalanceSpecification.exists_interior_subset_languageShift [Nonempty A]
    {L : Set (Word A)} (hL : IsFactorial L) (n : ℕ) :
    ∃ M : ℕ, ∀ w ∈ interiorLanguage L M, w.length = n →
      w ∈ language (languageShift L) := by sorry
