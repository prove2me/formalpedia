-- Prove2me | Theorems.Thm_BalanceSpecification_Growth_rate_le_of_tiling_bound
-- name    : BalanceSpecification.Growth.rate_le_of_tiling_bound
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T02:07:55.186773+00:00
-- url     : https://prove2.me/theorems/2754b845-4444-4f94-8940-410ff933009e
-- title:
--   Growth: rate le of tiling bound
-- statement:
--   An exponential bound along a positive-step arithmetic progression bounds
--   its sequence's actual limiting entropy. The finite end contribution is `2*M`.
--
--   Source: https://github.com/pseudorandom/balance_and_specification/blob/62771ced95e6f431064d40780b623362263ae9e4/BalanceSpecificaton/GrowthTiling.lean#L21-L45
-- source:
--   https://github.com/pseudorandom/balance_and_specification/blob/62771ced95e6f431064d40780b623362263ae9e4/BalanceSpecificaton/GrowthTiling.lean#L21-L45

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

theorem BalanceSpecification.Growth.rate_le_of_tiling_bound {a : ℕ → ℝ} (ha : ∀ n, 1 ≤ a n)
    (hs : Submultiplicative a) {n : ℕ} (hn : 0 < n) {M : ℕ} {C B : ℝ}
    (hC : 0 < C) (hB : 0 < B)
    (hbound : ∀ k : ℕ, a (2 * M + k * n) ≤ C * B ^ k) :
    rate a ≤ Real.log B / n := by sorry
