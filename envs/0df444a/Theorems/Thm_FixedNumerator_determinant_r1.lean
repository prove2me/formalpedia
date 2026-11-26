-- Prove2me | Theorems.Thm_FixedNumerator_determinant_r1
-- name    : FixedNumerator.determinant_r1
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T00:45:53.759727+00:00
-- url     : https://prove2.me/theorems/01977350-a4bd-584a-8c75-4955254a544f
-- title:
--   Fixed Numerator: determinant r1
-- statement:
--   **The determinant of case `r = 1`**: `‖a‖ ≤ N^{3/2}` and `σ ≥ 1` give
--   `‖1 + a w²‖ ≥ 1 - N^{-1/2} > 0`.
--
--   Source: https://github.com/jkfarland-bot/FixedNumerator/blob/817fb1416c9d54140c6bbdd9b2d08f37b481d934/Solution.lean#L159-L162
-- source:
--   https://github.com/jkfarland-bot/FixedNumerator/blob/817fb1416c9d54140c6bbdd9b2d08f37b481d934/Solution.lean#L159-L162

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

theorem FixedNumerator.determinant_r1 (N σ : ℝ) (hN : 1 < N) (a w : ℂ) (ha : ‖a‖ ≤ N ^ ((3 : ℝ) / 2))
    (hw : ‖w‖ = N ^ (-σ)) (hσ : 1 ≤ σ) :
    0 < 1 - N ^ (-(1 : ℝ) / 2) ∧ 1 - N ^ (-(1 : ℝ) / 2) ≤ ‖1 + a * w ^ 2‖ := by sorry
