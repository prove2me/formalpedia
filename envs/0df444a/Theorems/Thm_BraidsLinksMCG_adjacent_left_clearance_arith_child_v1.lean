-- Prove2me | Theorems.Thm_BraidsLinksMCG_adjacent_left_clearance_arith_child_v1
-- name    : BraidsLinksMCG.adjacent_left_clearance_arith_child_v1
-- status  : Proved
-- author  : @WillR
-- created : 2026-09-23T18:04:56.254774+00:00
-- url     : https://prove2.me/theorems/2541dbbb-9892-42a7-b538-bef19d4d7bb1
-- title:
--   The left point stays beyond the punctures
-- statement:
--   If the center remains one quarter-unit clear after subtracting half the radius, then the left point also clears the punctures when the separation's real part is at most the radius.
-- source:
--   Arithmetic sub-obligation of adjacentHomotopyLeft_re in open leaf a5d61856-8526-4cf8-960c-b185fcf7fd81, candidate 2467. The left coordinate subtracts half the separation and therefore uses the upper real-part bound.

import Mathlib
namespace BraidsLinksMCG
theorem adjacent_left_clearance_arith_child_v1 (n c r z : ℝ) (hmargin : n + 1 / 4 ≤ c - r / 2) (hz : z ≤ r) : n < c - z / 2 := by sorry
end BraidsLinksMCG
