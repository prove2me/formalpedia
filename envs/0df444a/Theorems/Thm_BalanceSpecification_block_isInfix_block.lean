-- Prove2me | Theorems.Thm_BalanceSpecification_block_isInfix_block
-- name    : BalanceSpecification.block_isInfix_block
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T02:08:10.616813+00:00
-- url     : https://prove2.me/theorems/00d441c1-6b3b-4ccd-b697-1689921d52b2
-- title:
--   Balance Specification: block is Infix block
-- statement:
--   A subinterval of coordinates produces a contiguous subword.
--
--   Source: https://github.com/pseudorandom/balance_and_specification/blob/62771ced95e6f431064d40780b623362263ae9e4/BalanceSpecificaton/FactorialEntropy.lean#L27-L43
-- source:
--   https://github.com/pseudorandom/balance_and_specification/blob/62771ced95e6f431064d40780b623362263ae9e4/BalanceSpecificaton/FactorialEntropy.lean#L27-L43

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

theorem BalanceSpecification.block_isInfix_block (x : Configuration A) (k l : ℤ) (n N : ℕ)
    (hleft : l ≤ k) (hright : k + n ≤ l + N) :
    block x k n <:+: block x l N := by sorry
