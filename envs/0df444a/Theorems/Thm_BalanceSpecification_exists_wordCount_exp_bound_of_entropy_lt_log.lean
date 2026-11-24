-- Prove2me | Theorems.Thm_BalanceSpecification_exists_wordCount_exp_bound_of_entropy_lt_log
-- name    : BalanceSpecification.exists_wordCount_exp_bound_of_entropy_lt_log
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-24T02:06:20.59164+00:00
-- url     : https://prove2.me/theorems/d19c5a4f-fdbe-4b24-b723-ef51234d5a31
-- title:
--   Balance Specification: exists word Count exp bound of entropy lt log
-- statement:
--   The corresponding actual shift-space envelope.
--
--   Source: https://github.com/pseudorandom/balance_and_specification/blob/62771ced95e6f431064d40780b623362263ae9e4/BalanceSpecificaton/GrowthUpperBounds.lean#L48-L54
-- source:
--   https://github.com/pseudorandom/balance_and_specification/blob/62771ced95e6f431064d40780b623362263ae9e4/BalanceSpecificaton/GrowthUpperBounds.lean#L48-L54

module
public import Definitions.Def_BalanceSpecificaton_Entropy
public import Mathlib.Tactic
public import Definitions.Def_BalanceSpecificaton_GrowthUpperBounds
set_option autoImplicit true
@[expose] public section
public section
noncomputable section
open Filter
open scoped Topology
open BalanceSpecification

theorem BalanceSpecification.exists_wordCount_exp_bound_of_entropy_lt_log
    {A : Type*} [Fintype A] [TopologicalSpace A] {X : ShiftSpace A}
    (hX : X.carrier.Nonempty) {γ : ℝ} (hγ : 0 < γ)
    (hgap : entropy X hX < Real.log γ) :
    ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, (wordCount (language X) n : ℝ) ≤ C * γ ^ n := by sorry
