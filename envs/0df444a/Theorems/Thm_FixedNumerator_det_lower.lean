-- Prove2me | Theorems.Thm_FixedNumerator_det_lower
-- name    : FixedNumerator.det_lower
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T00:38:05.881809+00:00
-- url     : https://prove2.me/theorems/4754b50d-b76b-48e6-b24f-e5710747949c
-- title:
--   Fixed Numerator: det lower
-- statement:
--   If `‖a‖ ≤ N^A` and `‖w‖ = N^{-σ}`, then `1 - N^{A - kσ} ≤ ‖1 + a w^k‖`.
--
--   Source: https://github.com/jkfarland-bot/FixedNumerator/blob/817fb1416c9d54140c6bbdd9b2d08f37b481d934/FixedNumerator/Determinant.lean#L31-L38
-- source:
--   https://github.com/jkfarland-bot/FixedNumerator/blob/817fb1416c9d54140c6bbdd9b2d08f37b481d934/FixedNumerator/Determinant.lean#L31-L38

module
public import Definitions.Def_FixedNumerator_Cases
public import Definitions.Def_FixedNumerator_Determinant
set_option autoImplicit true
@[expose] public section
public section
open Complex Real
open FixedNumerator

theorem FixedNumerator.det_lower {N A σ : ℝ} (hN : 0 < N) {a w : ℂ} (ha : ‖a‖ ≤ N ^ A) (hw : ‖w‖ = N ^ (-σ))
    (k : ℕ) : 1 - N ^ (A - k * σ) ≤ ‖1 + a * w ^ k‖ := by sorry
