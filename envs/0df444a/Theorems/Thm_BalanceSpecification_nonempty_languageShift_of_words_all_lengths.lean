-- Prove2me | Theorems.Thm_BalanceSpecification_nonempty_languageShift_of_words_all_lengths
-- name    : BalanceSpecification.nonempty_languageShift_of_words_all_lengths
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T01:48:06.771625+00:00
-- url     : https://prove2.me/theorems/5479f5d5-e870-47b3-80db-acc1b4c8bbc9
-- title:
--   Balance Specification: nonempty language Shift of words all lengths
-- statement:
--   If a factorial language has words of every length, its associated shift is nonempty.
--
--   Source: https://github.com/pseudorandom/balance_and_specification/blob/62771ced95e6f431064d40780b623362263ae9e4/BalanceSpecificaton/FactorialEntropy.lean#L197-L210
-- source:
--   https://github.com/pseudorandom/balance_and_specification/blob/62771ced95e6f431064d40780b623362263ae9e4/BalanceSpecificaton/FactorialEntropy.lean#L197-L210

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

theorem BalanceSpecification.nonempty_languageShift_of_words_all_lengths [Nonempty A]
    {L : Set (Word A)} (hL : IsFactorial L)
    (hlen : ∀ n : ℕ, ∃ w ∈ L, w.length = n) : (languageShift L).carrier.Nonempty := by sorry
