-- Prove2me | Theorems.Thm_FixedNumerator_delta_coupled_lower
-- name    : FixedNumerator.delta_coupled_lower
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T00:40:07.899039+00:00
-- url     : https://prove2.me/theorems/49b4be18-1380-5721-bb29-42ee4fc20771
-- title:
--   Fixed Numerator: delta coupled lower
-- statement:
--   **The determinant of the coupled pair** (cases `r = 0, 2`).
--
--   Source: https://github.com/jkfarland-bot/FixedNumerator/blob/817fb1416c9d54140c6bbdd9b2d08f37b481d934/FixedNumerator/Determinant.lean#L74-L85
-- source:
--   https://github.com/jkfarland-bot/FixedNumerator/blob/817fb1416c9d54140c6bbdd9b2d08f37b481d934/FixedNumerator/Determinant.lean#L74-L85

module
public import Definitions.Def_FixedNumerator_Cases
public import Definitions.Def_FixedNumerator_Determinant
set_option autoImplicit true
@[expose] public section
public section
open Complex Real
open FixedNumerator

theorem FixedNumerator.delta_coupled_lower {N σ : ℝ} (hN : 1 < N) {a₁ a₃ w : ℂ}
    (ha₁ : ‖a₁‖ ≤ N ^ ((1 : ℝ) / 2)) (ha₃ : ‖a₃‖ ≤ N ^ ((5 : ℝ) / 2)) (hw : ‖w‖ = N ^ (-σ))
    (hσ : 1 ≤ σ) :
    0 < 1 - N ^ (-1 : ℝ) ∧ 1 - N ^ (-1 : ℝ) ≤ ‖1 - a₁ * a₃ * w ^ 4‖ := by sorry
