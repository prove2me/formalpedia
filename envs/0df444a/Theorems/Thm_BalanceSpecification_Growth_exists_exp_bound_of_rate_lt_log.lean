-- Prove2me | Theorems.Thm_BalanceSpecification_Growth_exists_exp_bound_of_rate_lt_log
-- name    : BalanceSpecification.Growth.exists_exp_bound_of_rate_lt_log
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T02:06:17.331425+00:00
-- url     : https://prove2.me/theorems/b2734307-9e00-4993-9701-114b5d614744
-- title:
--   Growth: exists exp bound of rate lt log
-- statement:
--   Any base strictly above the limiting growth gives a uniform exponential
--   upper envelope, without a bounded-supermultiplicativity hypothesis.
--
--   Source: https://github.com/pseudorandom/balance_and_specification/blob/62771ced95e6f431064d40780b623362263ae9e4/BalanceSpecificaton/GrowthUpperBounds.lean#L19-L41
-- source:
--   https://github.com/pseudorandom/balance_and_specification/blob/62771ced95e6f431064d40780b623362263ae9e4/BalanceSpecificaton/GrowthUpperBounds.lean#L19-L41

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
open BalanceSpecification BalanceSpecification.Growth

theorem BalanceSpecification.Growth.exists_exp_bound_of_rate_lt_log {a : ℕ → ℝ} (ha : ∀ n, 1 ≤ a n)
    (hs : Submultiplicative a) {γ : ℝ} (hγ : 0 < γ)
    (hgap : rate a < Real.log γ) :
    ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, a n ≤ C * γ ^ n := by sorry
