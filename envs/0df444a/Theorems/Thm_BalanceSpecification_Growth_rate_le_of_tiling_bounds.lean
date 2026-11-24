-- Prove2me | Theorems.Thm_BalanceSpecification_Growth_rate_le_of_tiling_bounds
-- name    : BalanceSpecification.Growth.rate_le_of_tiling_bounds
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T02:08:02.925583+00:00
-- url     : https://prove2.me/theorems/19089a1e-ec84-413b-9a02-b4f74f706ed9
-- title:
--   Growth: rate le of tiling bounds
-- statement:
--   If every positive block size gives a tiling estimate against `b`, the
--   entropy of `a` is at most the infimum of the logarithmic rates of `b`.
--
--   Source: https://github.com/pseudorandom/balance_and_specification/blob/62771ced95e6f431064d40780b623362263ae9e4/BalanceSpecificaton/GrowthTiling.lean#L49-L61
-- source:
--   https://github.com/pseudorandom/balance_and_specification/blob/62771ced95e6f431064d40780b623362263ae9e4/BalanceSpecificaton/GrowthTiling.lean#L49-L61

module
public import Definitions.Def_BalanceSpecificaton_Growth
public import Mathlib.Tactic
public import Definitions.Def_BalanceSpecificaton_GrowthTiling
set_option autoImplicit true
@[expose] public section
public section
noncomputable section
open Set Filter
open scoped Topology
open BalanceSpecification BalanceSpecification.Growth

theorem BalanceSpecification.Growth.rate_le_of_tiling_bounds {a b : ℕ → ℝ} (ha : ∀ n, 1 ≤ a n)
    (hb : ∀ n, 1 ≤ b n) (hsa : Submultiplicative a)
    (hbound : ∀ n : ℕ, 0 < n → ∃ M : ℕ, ∃ C : ℝ, 0 < C ∧
      ∀ k : ℕ, a (2 * M + k * n) ≤ C * (b n) ^ k) :
    rate a ≤ rate b := by sorry
