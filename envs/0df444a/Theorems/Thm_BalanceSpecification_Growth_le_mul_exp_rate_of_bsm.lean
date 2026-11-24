-- Prove2me | Theorems.Thm_BalanceSpecification_Growth_le_mul_exp_rate_of_bsm
-- name    : BalanceSpecification.Growth.le_mul_exp_rate_of_bsm
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T01:52:52.263941+00:00
-- url     : https://prove2.me/theorems/d38d093e-d2d6-4c68-a50a-90fc36d9486c
-- title:
--   Growth: le mul exp rate of bsm
-- statement:
--   A boundedly supermultiplicative sequence differs from its entropy exponential
--   by at most the same multiplicative constant.
--
--   Source: https://github.com/pseudorandom/balance_and_specification/blob/62771ced95e6f431064d40780b623362263ae9e4/BalanceSpecificaton/Growth.lean#L72-L106
-- source:
--   https://github.com/pseudorandom/balance_and_specification/blob/62771ced95e6f431064d40780b623362263ae9e4/BalanceSpecificaton/Growth.lean#L72-L106

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

theorem BalanceSpecification.Growth.le_mul_exp_rate_of_bsm {a : ℕ → ℝ} (ha : ∀ n, 1 ≤ a n)
    (hs : Submultiplicative a) {c : ℝ} (hc : 1 ≤ c)
    (hb : ∀ m n, a m * a n ≤ c * a (m + n)) (n : ℕ) :
    a n ≤ c * Real.exp ((n : ℝ) * rate a) := by sorry
