-- Prove2me | Theorems.Thm_BalanceSpecification_Growth_bsm_iff_exp_ratio
-- name    : BalanceSpecification.Growth.bsm_iff_exp_ratio
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T01:52:52.08907+00:00
-- url     : https://prove2.me/theorems/8775aede-27cf-4ea7-b291-e002bb0391dd
-- title:
--   Growth: bsm iff exp ratio
-- statement:
--   The exact ratio form of the paper's BSM entropy criterion, for positive
--   submultiplicative numerical sequences. The shift-space specialization additionally
--   needs its word-count submultiplicativity theorem.
--
--   Source: https://github.com/pseudorandom/balance_and_specification/blob/62771ced95e6f431064d40780b623362263ae9e4/BalanceSpecificaton/Growth.lean#L140-L159
-- source:
--   https://github.com/pseudorandom/balance_and_specification/blob/62771ced95e6f431064d40780b623362263ae9e4/BalanceSpecificaton/Growth.lean#L140-L159

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

theorem BalanceSpecification.Growth.bsm_iff_exp_ratio {a : ℕ → ℝ} (ha : ∀ n, 1 ≤ a n)
    (hs : Submultiplicative a) :
    BoundedSupermultiplicative a ↔
      ∃ c : ℝ, 1 ≤ c ∧ ∀ n : ℕ,
        1 / c ≤ Real.exp ((n : ℝ) * rate a) / a n ∧
          Real.exp ((n : ℝ) * rate a) / a n ≤ 1 := by sorry
