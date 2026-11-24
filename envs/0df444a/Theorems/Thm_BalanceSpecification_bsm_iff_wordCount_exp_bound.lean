-- Prove2me | Theorems.Thm_BalanceSpecification_bsm_iff_wordCount_exp_bound
-- name    : BalanceSpecification.bsm_iff_wordCount_exp_bound
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T01:41:51.379945+00:00
-- url     : https://prove2.me/theorems/1b3cf3da-fead-42dc-82b5-1df9fdb6bc45
-- title:
--   Balance Specification: bsm iff word Count exp bound
-- statement:
--   The equivalent envelope form, useful in the coded-system construction.
--
--   Source: https://github.com/pseudorandom/balance_and_specification/blob/62771ced95e6f431064d40780b623362263ae9e4/BalanceSpecificaton/Entropy.lean#L61-L65
-- source:
--   https://github.com/pseudorandom/balance_and_specification/blob/62771ced95e6f431064d40780b623362263ae9e4/BalanceSpecificaton/Entropy.lean#L61-L65

module
public import Definitions.Def_BalanceSpecificaton_CountBounds
public import Definitions.Def_BalanceSpecificaton_Growth
public import Mathlib.Tactic
public import Definitions.Def_BalanceSpecificaton_Entropy
set_option autoImplicit true
@[expose] public section
public section
noncomputable section
open Filter
open scoped Topology
open BalanceSpecification
variable {A : Type*} [Fintype A] [TopologicalSpace A]

theorem BalanceSpecification.bsm_iff_wordCount_exp_bound {X : ShiftSpace A} (hX : X.carrier.Nonempty) :
    BoundedlySupermultiplicative (language X) ↔
      ∃ c : ℝ, 1 ≤ c ∧ ∀ n : ℕ,
        (wordCount (language X) n : ℝ) ≤ c * Real.exp ((n : ℝ) * entropy X hX) := by sorry
