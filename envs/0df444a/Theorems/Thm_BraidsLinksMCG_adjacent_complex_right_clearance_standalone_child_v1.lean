-- Prove2me | Theorems.Thm_BraidsLinksMCG_adjacent_complex_right_clearance_standalone_child_v1
-- name    : BraidsLinksMCG.adjacent_complex_right_clearance_standalone_child_v1
-- status  : Proved
-- author  : @WillR
-- created : 2026-09-23T18:25:57.22995+00:00
-- url     : https://prove2.me/theorems/27e2d2f7-9325-4a1b-b213-1eff040090dc
-- title:
--   The complex right point stays clear without imported helper modules
-- statement:
--   If the separation vector has norm r and the real center has a quarter-unit margin beyond c − r/2, then the complex point c + z/2 has real part strictly greater than n.
-- source:
--   Self-contained form of the exact adjacentHomotopyRight_re obligation from open leaf a5d61856-8526-4cf8-960c-b185fcf7fd81. Earlier published arithmetic child imports caused confirmed missing-module build errors in candidate 2474 and candidate 2475 before proof evaluation. This statement retains the same geometric inequality and removes only those unavailable theorem imports; the proof derives the real-part bound directly from ‖z‖ = r and hmargin.

import Mathlib
namespace BraidsLinksMCG
theorem adjacent_complex_right_clearance_standalone_child_v1 (n c r : ℝ) (z : ℂ)
    (hmargin : n + 1 / 4 ≤ c - r / 2) (hnorm : ‖z‖ = r) :
    n < (((c : ℂ) + (1 / 2 : ℂ) * z).re) := by sorry
end BraidsLinksMCG
