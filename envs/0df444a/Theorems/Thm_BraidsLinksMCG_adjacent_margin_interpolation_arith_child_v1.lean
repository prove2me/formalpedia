-- Prove2me | Theorems.Thm_BraidsLinksMCG_adjacent_margin_interpolation_arith_child_v1
-- name    : BraidsLinksMCG.adjacent_margin_interpolation_arith_child_v1
-- status  : Proved
-- author  : @WillR
-- created : 2026-09-23T17:15:31.707452+00:00
-- url     : https://prove2.me/theorems/d8f816d7-bd0c-481e-90c7-fa0af4f71263
-- title:
--   Linear interpolation preserves adjacent clearance
-- statement:
--   If a source center has one quarter-unit clearance, linearly moving it to n plus three halves while interpolating its radius to one preserves that clearance throughout the unit interval.
-- source:
--   Arithmetic sub-obligation from the affine interpolation stage of adjacentHomotopyMargin in open leaf a5d61856-8526-4cf8-960c-b185fcf7fd81, candidate 2463. It isolates the exact center and radius interpolation formulas.

import Mathlib
namespace BraidsLinksMCG
theorem adjacent_margin_interpolation_arith_child_v1 (n : ℕ) (c r s : ℝ) (hsource : (n : ℝ) + 1 / 4 ≤ c - r / 2) (hs0 : 0 ≤ s) (hs1 : s ≤ 1) : (n : ℝ) + 1 / 4 ≤ (1 - s) * c + s * ((n : ℝ) + 3 / 2) - ((1 - s) * r + s) / 2 := by sorry
end BraidsLinksMCG
