-- Prove2me | Theorems.Thm_BalanceSpecification_Growth_rate_nonneg
-- name    : BalanceSpecification.Growth.rate_nonneg
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T01:53:32.660392+00:00
-- url     : https://prove2.me/theorems/b6275319-ea11-4bd3-a792-7d5c9a367413
-- title:
--   Growth: rate nonneg
-- statement:
--   Positive counts have nonnegative limiting logarithmic growth.
--
--   Source: https://github.com/pseudorandom/balance_and_specification/blob/62771ced95e6f431064d40780b623362263ae9e4/BalanceSpecificaton/Growth.lean#L162-L165
-- source:
--   https://github.com/pseudorandom/balance_and_specification/blob/62771ced95e6f431064d40780b623362263ae9e4/BalanceSpecificaton/Growth.lean#L162-L165

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

theorem BalanceSpecification.Growth.rate_nonneg {a : ℕ → ℝ} (ha : ∀ n, 1 ≤ a n)
    (hs : Submultiplicative a) : 0 ≤ rate a := by sorry
