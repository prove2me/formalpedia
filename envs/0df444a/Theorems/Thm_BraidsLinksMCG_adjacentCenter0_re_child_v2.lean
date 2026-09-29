-- Prove2me | Theorems.Thm_BraidsLinksMCG_adjacentCenter0_re_child_v2
-- name    : BraidsLinksMCG.adjacentCenter0_re_child_v2
-- status  : Proved
-- author  : @WillR
-- created : 2026-09-23T16:30:48.779771+00:00
-- url     : https://prove2.me/theorems/04b91ab1-00fe-4fe4-95ed-0437875461b3
-- title:
--   Real part of the adjacent moving center
-- statement:
--   For the adjacent-strand construction, the real part of the center (n + 1) + w/2 is n + 1 plus half the real part of the strand separation w.
-- source:
--   Minimal algebraic sublemma extracted from adjacentCenter0 in candidate 2457 for open leaf a5d61856-8526-4cf8-960c-b185fcf7fd81. It isolates the hcenter real-part calculation without copying the failing geometric proof prefix.

import Mathlib
namespace BraidsLinksMCG
theorem adjacentCenter0_re_child_v2 (n : ℕ) (w : ℂ) : (((n : ℝ) + 1 : ℂ) + (1 / 2 : ℂ) * w).re = (n : ℝ) + 1 + (1 / 2 : ℝ) * w.re := by sorry
end BraidsLinksMCG
