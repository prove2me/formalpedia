-- Prove2me | Theorems.Thm_BalanceSpecification_Growth_bsm_iff_uniform_exp_bound
-- name    : BalanceSpecification.Growth.bsm_iff_uniform_exp_bound
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T01:41:49.203819+00:00
-- url     : https://prove2.me/theorems/536547e9-af09-4424-a5c2-ae3b754fa002
-- title:
--   Growth: bsm iff uniform exp bound
-- statement:
--   BSM is equivalent to a uniform exponential upper bound with the actual
--   limiting growth rate.
--
--   Source: https://github.com/pseudorandom/balance_and_specification/blob/62771ced95e6f431064d40780b623362263ae9e4/BalanceSpecificaton/Growth.lean#L115-L135
-- source:
--   https://github.com/pseudorandom/balance_and_specification/blob/62771ced95e6f431064d40780b623362263ae9e4/BalanceSpecificaton/Growth.lean#L115-L135

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

theorem BalanceSpecification.Growth.bsm_iff_uniform_exp_bound {a : ℕ → ℝ} (ha : ∀ n, 1 ≤ a n)
    (hs : Submultiplicative a) :
    BoundedSupermultiplicative a ↔
      ∃ c : ℝ, 1 ≤ c ∧ ∀ n, a n ≤ c * Real.exp ((n : ℝ) * rate a) := by sorry
