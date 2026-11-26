-- Prove2me | Theorems.Thm_FixedNumerator_determinant_r3
-- name    : FixedNumerator.determinant_r3
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T00:46:46.550201+00:00
-- url     : https://prove2.me/theorems/aaf03797-5ceb-49ca-ab2b-83845aff22d3
-- title:
--   Fixed Numerator: determinant r3
-- statement:
--   **The determinant of case `r = 3`** (DDHL's `Δ(s, ℓ; π)`): `‖a‖ ≤ N³` and `σ ≥ 1` give
--   `‖1 + a w⁴‖ ≥ 1 - N^{-1} > 0`.
--
--   Source: https://github.com/jkfarland-bot/FixedNumerator/blob/817fb1416c9d54140c6bbdd9b2d08f37b481d934/Solution.lean#L166-L169
-- source:
--   https://github.com/jkfarland-bot/FixedNumerator/blob/817fb1416c9d54140c6bbdd9b2d08f37b481d934/Solution.lean#L166-L169

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

theorem FixedNumerator.determinant_r3 (N σ : ℝ) (hN : 1 < N) (a w : ℂ) (ha : ‖a‖ ≤ N ^ (3 : ℝ))
    (hw : ‖w‖ = N ^ (-σ)) (hσ : 1 ≤ σ) :
    0 < 1 - N ^ (-1 : ℝ) ∧ 1 - N ^ (-1 : ℝ) ≤ ‖1 + a * w ^ 4‖ := by sorry
