-- Prove2me | Theorems.Thm_FixedNumerator_determinant_coupled
-- name    : FixedNumerator.determinant_coupled
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T00:46:28.736807+00:00
-- url     : https://prove2.me/theorems/f1048456-b860-5a71-aefd-5d92d2cad8ae
-- title:
--   Fixed Numerator: determinant coupled
-- statement:
--   **The determinant of the coupled pair**: `‖a₁‖ ≤ N^{1/2}`, `‖a₃‖ ≤ N^{5/2}` and `σ ≥ 1` give
--   `‖1 - a₁ a₃ w⁴‖ ≥ 1 - N^{-1} > 0`.
--
--   Source: https://github.com/jkfarland-bot/FixedNumerator/blob/817fb1416c9d54140c6bbdd9b2d08f37b481d934/Solution.lean#L173-L177
-- source:
--   https://github.com/jkfarland-bot/FixedNumerator/blob/817fb1416c9d54140c6bbdd9b2d08f37b481d934/Solution.lean#L173-L177

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

theorem FixedNumerator.determinant_coupled (N σ : ℝ) (hN : 1 < N) (a₁ a₃ w : ℂ)
    (ha₁ : ‖a₁‖ ≤ N ^ ((1 : ℝ) / 2)) (ha₃ : ‖a₃‖ ≤ N ^ ((5 : ℝ) / 2)) (hw : ‖w‖ = N ^ (-σ))
    (hσ : 1 ≤ σ) :
    0 < 1 - N ^ (-1 : ℝ) ∧ 1 - N ^ (-1 : ℝ) ≤ ‖1 - a₁ * a₃ * w ^ 4‖ := by sorry
