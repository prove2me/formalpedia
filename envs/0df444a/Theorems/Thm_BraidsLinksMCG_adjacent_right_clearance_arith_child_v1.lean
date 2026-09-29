-- Prove2me | Theorems.Thm_BraidsLinksMCG_adjacent_right_clearance_arith_child_v1
-- name    : BraidsLinksMCG.adjacent_right_clearance_arith_child_v1
-- status  : Proved
-- author  : @WillR
-- created : 2026-09-23T18:04:53.529769+00:00
-- url     : https://prove2.me/theorems/cddbbb06-3805-4c69-92ce-94a3cfde4a96
-- title:
--   The right point stays beyond the punctures
-- statement:
--   If the center remains one quarter-unit clear after subtracting half the radius, then the right point also clears the punctures when the separation's real part is at least minus the radius.
-- source:
--   Arithmetic sub-obligation of adjacentHomotopyRight_re in open leaf a5d61856-8526-4cf8-960c-b185fcf7fd81, candidate 2467. The right coordinate adds half the separation and therefore uses the lower real-part bound.

import Mathlib
namespace BraidsLinksMCG
theorem adjacent_right_clearance_arith_child_v1 (n c r z : ℝ) (hmargin : n + 1 / 4 ≤ c - r / 2) (hz : -r ≤ z) : n < c + z / 2 := by sorry
end BraidsLinksMCG
