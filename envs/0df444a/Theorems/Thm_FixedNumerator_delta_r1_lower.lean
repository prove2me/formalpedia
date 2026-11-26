-- Prove2me | Theorems.Thm_FixedNumerator_delta_r1_lower
-- name    : FixedNumerator.delta_r1_lower
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T00:39:56.780641+00:00
-- url     : https://prove2.me/theorems/11cb8de8-d5a0-5506-bc5f-21a9d2b34214
-- title:
--   Fixed Numerator: delta r1 lower
-- statement:
--   **The determinant of case `r = 1`.**
--
--   Source: https://github.com/jkfarland-bot/FixedNumerator/blob/817fb1416c9d54140c6bbdd9b2d08f37b481d934/FixedNumerator/Determinant.lean#L50-L59
-- source:
--   https://github.com/jkfarland-bot/FixedNumerator/blob/817fb1416c9d54140c6bbdd9b2d08f37b481d934/FixedNumerator/Determinant.lean#L50-L59

module
public import Definitions.Def_FixedNumerator_Cases
public import Definitions.Def_FixedNumerator_Determinant
set_option autoImplicit true
@[expose] public section
public section
open Complex Real
open FixedNumerator

theorem FixedNumerator.delta_r1_lower {N σ : ℝ} (hN : 1 < N) {a w : ℂ} (ha : ‖a‖ ≤ N ^ ((3 : ℝ) / 2))
    (hw : ‖w‖ = N ^ (-σ)) (hσ : 1 ≤ σ) :
    0 < 1 - N ^ (-(1 : ℝ) / 2) ∧ 1 - N ^ (-(1 : ℝ) / 2) ≤ ‖1 + a * w ^ 2‖ := by sorry
