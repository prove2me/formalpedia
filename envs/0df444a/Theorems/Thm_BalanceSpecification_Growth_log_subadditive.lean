-- Prove2me | Theorems.Thm_BalanceSpecification_Growth_log_subadditive
-- name    : BalanceSpecification.Growth.log_subadditive
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T01:44:44.600734+00:00
-- url     : https://prove2.me/theorems/36adbc7f-c5d9-4475-9d96-8b7030599581
-- title:
--   Growth: log subadditive
-- statement:
--   Submultiplicative positive counts have subadditive logarithms.
--
--   Source: https://github.com/pseudorandom/balance_and_specification/blob/62771ced95e6f431064d40780b623362263ae9e4/BalanceSpecificaton/Growth.lean#L28-L35
-- source:
--   https://github.com/pseudorandom/balance_and_specification/blob/62771ced95e6f431064d40780b623362263ae9e4/BalanceSpecificaton/Growth.lean#L28-L35

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

theorem BalanceSpecification.Growth.log_subadditive {a : ℕ → ℝ} (ha : ∀ n, 1 ≤ a n)
    (hs : Submultiplicative a) : Subadditive (fun n => Real.log (a n)) := by sorry
