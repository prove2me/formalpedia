-- Prove2me | Theorems.Thm_BalanceSpecification_Growth_exp_mul_rate_le
-- name    : BalanceSpecification.Growth.exp_mul_rate_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T01:41:44.893809+00:00
-- url     : https://prove2.me/theorems/37b9717e-5301-452d-bce1-9a9d54ee448c
-- title:
--   Growth: exp mul rate le
-- statement:
--   The entropy exponential is a lower bound on every word count.
--
--   Source: https://github.com/pseudorandom/balance_and_specification/blob/62771ced95e6f431064d40780b623362263ae9e4/BalanceSpecificaton/Growth.lean#L57-L68
-- source:
--   https://github.com/pseudorandom/balance_and_specification/blob/62771ced95e6f431064d40780b623362263ae9e4/BalanceSpecificaton/Growth.lean#L57-L68

module
public import Mathlib.Analysis.Subadditive
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Topology.Order.LiminfLimsup
public import Mathlib.Tactic
public import Definitions.Def_BalanceSpecificaton_Growth
set_option autoImplicit true
@[expose] public section
public section
noncomputable section
open Set Filter
open scoped Topology
open BalanceSpecification BalanceSpecification.Growth

theorem BalanceSpecification.Growth.exp_mul_rate_le {a : ℕ → ℝ} (ha : ∀ n, 1 ≤ a n)
    (hs : Submultiplicative a) (n : ℕ) :
    Real.exp ((n : ℝ) * rate a) ≤ a n := by sorry
