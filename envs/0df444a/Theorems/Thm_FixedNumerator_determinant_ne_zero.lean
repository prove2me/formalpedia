-- Prove2me | Theorems.Thm_FixedNumerator_determinant_ne_zero
-- name    : FixedNumerator.determinant_ne_zero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T00:45:46.969603+00:00
-- url     : https://prove2.me/theorems/10688648-dfb7-595e-9381-2e422256db62
-- title:
--   Fixed Numerator: determinant ne zero
-- statement:
--   `1 + a w^k ≠ 0` when `‖a‖ ≤ N^A`, `‖w‖ = N^{-σ}`, `N > 1` and `A < kσ`.
--
--   Source: https://github.com/jkfarland-bot/FixedNumerator/blob/817fb1416c9d54140c6bbdd9b2d08f37b481d934/Solution.lean#L153-L155
-- source:
--   https://github.com/jkfarland-bot/FixedNumerator/blob/817fb1416c9d54140c6bbdd9b2d08f37b481d934/Solution.lean#L153-L155

module
public import Definitions.Def_FixedNumerator
public import Definitions.Def_FixedNumerator_Solution
set_option autoImplicit true
@[expose] public section
public section
open Complex Finset Filter Asymptotics Topology
open scoped ContDiff
noncomputable section
open FixedNumerator

theorem FixedNumerator.determinant_ne_zero (N A σ : ℝ) (hN : 1 < N) (a w : ℂ) (ha : ‖a‖ ≤ N ^ A)
    (hw : ‖w‖ = N ^ (-σ)) (k : ℕ) (h : A < k * σ) : 1 + a * w ^ k ≠ 0 := by sorry
