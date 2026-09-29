-- Prove2me | Theorems.Thm_BraidsLinksMCG_adjacent_source_margin_arith_child_v1
-- name    : BraidsLinksMCG.adjacent_source_margin_arith_child_v1
-- status  : Proved
-- author  : @WillR
-- created : 2026-09-23T17:15:33.168243+00:00
-- url     : https://prove2.me/theorems/96660c33-628b-41ba-867c-c532d91c4494
-- title:
--   The adjacent source configuration has positive clearance
-- statement:
--   If the moving radius is at most one and the separation's real part is at least minus one half, the source center remains one quarter-unit clear after subtracting half the radius.
-- source:
--   Arithmetic sub-obligation from the hsource stage of adjacentHomotopyMargin in open leaf a5d61856-8526-4cf8-960c-b185fcf7fd81, candidate 2463. It isolates the exact radius and separation bounds used by the source configuration.

import Mathlib
namespace BraidsLinksMCG
theorem adjacent_source_margin_arith_child_v1 (n : ℕ) (r : ℝ) (z : ℂ) (hr : r ≤ 1) (hz : -(1 / 2 : ℝ) ≤ z.re) : (n : ℝ) + 1 / 4 ≤ (n : ℝ) + 1 + (1 / 2 : ℝ) * z.re - r / 2 := by sorry
end BraidsLinksMCG
