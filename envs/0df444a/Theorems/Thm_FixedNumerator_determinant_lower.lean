-- Prove2me | Theorems.Thm_FixedNumerator_determinant_lower
-- name    : FixedNumerator.determinant_lower
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T00:45:39.390043+00:00
-- url     : https://prove2.me/theorems/68f1fb81-2a33-5b14-9e08-976284a4a50c
-- title:
--   Fixed Numerator: determinant lower
-- statement:
--   If `‖a‖ ≤ N^A` and `‖w‖ = N^{-σ}`, then `1 - N^{A - kσ} ≤ ‖1 + a w^k‖`.
--
--   Source: https://github.com/jkfarland-bot/FixedNumerator/blob/817fb1416c9d54140c6bbdd9b2d08f37b481d934/Solution.lean#L148-L150
-- source:
--   https://github.com/jkfarland-bot/FixedNumerator/blob/817fb1416c9d54140c6bbdd9b2d08f37b481d934/Solution.lean#L148-L150

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

theorem FixedNumerator.determinant_lower (N A σ : ℝ) (hN : 0 < N) (a w : ℂ) (ha : ‖a‖ ≤ N ^ A)
    (hw : ‖w‖ = N ^ (-σ)) (k : ℕ) : 1 - N ^ (A - k * σ) ≤ ‖1 + a * w ^ k‖ := by sorry
