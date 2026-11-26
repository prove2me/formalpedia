-- Prove2me | Theorems.Thm_FixedNumerator_det_ne_zero
-- name    : FixedNumerator.det_ne_zero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T00:39:55.300522+00:00
-- url     : https://prove2.me/theorems/02dc0cf9-c65a-5280-85fa-48262f3851e6
-- title:
--   Fixed Numerator: det ne zero
-- statement:
--   `1 + a w^k ≠ 0` when `‖a‖ ≤ N^A`, `‖w‖ = N^{-σ}`, `N > 1` and `A < kσ`.
--
--   Source: https://github.com/jkfarland-bot/FixedNumerator/blob/817fb1416c9d54140c6bbdd9b2d08f37b481d934/FixedNumerator/Determinant.lean#L41-L47
-- source:
--   https://github.com/jkfarland-bot/FixedNumerator/blob/817fb1416c9d54140c6bbdd9b2d08f37b481d934/FixedNumerator/Determinant.lean#L41-L47

module
public import Definitions.Def_FixedNumerator_Cases
public import Definitions.Def_FixedNumerator_Determinant
set_option autoImplicit true
@[expose] public section
public section
open Complex Real
open FixedNumerator

theorem FixedNumerator.det_ne_zero {N A σ : ℝ} (hN : 1 < N) {a w : ℂ} (ha : ‖a‖ ≤ N ^ A)
    (hw : ‖w‖ = N ^ (-σ)) (k : ℕ) (h : A < k * σ) : 1 + a * w ^ k ≠ 0 := by sorry
