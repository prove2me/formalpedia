-- Prove2me | Theorems.Thm_FixedNumerator_delta_r3_lower
-- name    : FixedNumerator.delta_r3_lower
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T00:38:31.660854+00:00
-- url     : https://prove2.me/theorems/fd3fe884-c7f8-44a6-ab4f-c06105a001c5
-- title:
--   Fixed Numerator: delta r3 lower
-- statement:
--   **The determinant of case `r = 3`**, DDHL's `Δ(s, ℓ; π)`.
--
--   Source: https://github.com/jkfarland-bot/FixedNumerator/blob/817fb1416c9d54140c6bbdd9b2d08f37b481d934/FixedNumerator/Determinant.lean#L62-L71
-- source:
--   https://github.com/jkfarland-bot/FixedNumerator/blob/817fb1416c9d54140c6bbdd9b2d08f37b481d934/FixedNumerator/Determinant.lean#L62-L71

module
public import Definitions.Def_FixedNumerator_Cases
public import Definitions.Def_FixedNumerator_Determinant
set_option autoImplicit true
@[expose] public section
public section
open Complex Real
open FixedNumerator

theorem FixedNumerator.delta_r3_lower {N σ : ℝ} (hN : 1 < N) {a w : ℂ} (ha : ‖a‖ ≤ N ^ (3 : ℝ))
    (hw : ‖w‖ = N ^ (-σ)) (hσ : 1 ≤ σ) :
    0 < 1 - N ^ (-1 : ℝ) ∧ 1 - N ^ (-1 : ℝ) ≤ ‖1 + a * w ^ 4‖ := by sorry
