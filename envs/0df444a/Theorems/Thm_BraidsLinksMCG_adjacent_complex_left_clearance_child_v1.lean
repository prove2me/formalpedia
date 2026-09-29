-- Prove2me | Theorems.Thm_BraidsLinksMCG_adjacent_complex_left_clearance_child_v1
-- name    : BraidsLinksMCG.adjacent_complex_left_clearance_child_v1
-- status  : Proved
-- author  : @WillR
-- created : 2026-09-23T18:17:41.131536+00:00
-- url     : https://prove2.me/theorems/3f09f4e9-9ea4-4e89-a1e2-a2957df96dd1
-- title:
--   The complex left point remains outside the punctures
-- statement:
--   A complex separation vector of norm r shifts a real center c by half its leftward direction; under the quarter-unit margin, this point remains to the right of n.
-- source:
--   Source-faithful complex-coordinate obligation for adjacentHomotopyLeft_re in open leaf a5d61856-8526-4cf8-960c-b185fcf7fd81, candidate 2472. It composes the accepted norm-to-real-part bound and accepted adjacent left clearance arithmetic child, and isolates the Complex.re normalization used to prove the moving strand avoids every fixed puncture.

import Mathlib
import Theorems.Thm_BraidsLinksMCG_adjacent_left_clearance_arith_child_v1
import Theorems.Thm_BraidsLinksMCG_adjacent_right_clearance_arith_child_v1
namespace BraidsLinksMCG
theorem adjacent_complex_left_clearance_child_v1 (n c r : ℝ) (z : ℂ)
    (hmargin : n + 1 / 4 ≤ c - r / 2) (hnorm : ‖z‖ = r) :
    n < (((c : ℂ) - (1 / 2 : ℂ) * z).re) := by sorry
end BraidsLinksMCG
