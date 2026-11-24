-- Prove2me | Theorems.Thm_BalanceSpecification_isClosed_block_mem
-- name    : BalanceSpecification.isClosed_block_mem
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-24T02:08:23.295129+00:00
-- url     : https://prove2.me/theorems/272ee6c9-a47e-4eba-aeb4-65888030d53f
-- title:
--   Balance Specification: is Closed block mem
-- statement:
--   Prescribing that a fixed-length block belongs to a language is a closed condition.
--
--   Source: https://github.com/pseudorandom/balance_and_specification/blob/62771ced95e6f431064d40780b623362263ae9e4/BalanceSpecificaton/FactorialEntropy.lean#L87-L106
-- source:
--   https://github.com/pseudorandom/balance_and_specification/blob/62771ced95e6f431064d40780b623362263ae9e4/BalanceSpecificaton/FactorialEntropy.lean#L87-L106

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

theorem BalanceSpecification.isClosed_block_mem (L : Set (Word A)) (k : ℤ) (n : ℕ) :
    IsClosed {x : Configuration A | block x k n ∈ L} := by sorry
