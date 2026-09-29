-- Prove2me | Theorems.Thm_BraidsLinksMCG_adjacentRadialProfileFormulas_child_v2
-- name    : BraidsLinksMCG.adjacentRadialProfileFormulas_child_v2
-- status  : Proved
-- author  : @WillR
-- created : 2026-09-23T22:47:24.609704+00:00
-- url     : https://prove2.me/theorems/1fdba6dc-9b9e-4dfc-9be3-f5b52b9c2033
-- title:
--   The adjacent radial radius and turn profiles are piecewise elementary
-- statement:
--   On the unit interval, the max/min radius and angular-turn expressions used in the adjacent radial/profile path have the exact three-piece formulas before, during, and after the half-turn. The proposition is stated directly without auxiliary declarations so it can be materialized as a theorem-only child.
-- source:
--   The max/min expressions and breakpoints are taken verbatim from the adjacent radial/profile path construction in adjacent_candidate_work_v28.lean; this child isolates its first, middle, and final piecewise scalar calculations.

import Mathlib

namespace BraidsLinksMCG

theorem adjacentRadialProfileFormulas_child_v2 (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    ((t ≤ 1 / 2 → max (1 - t) (max (1 / 2) (2 * t - 1)) = 1 - t) ∧
      (1 / 2 ≤ t → t ≤ 3 / 4 → max (1 - t) (max (1 / 2) (2 * t - 1)) = 1 / 2) ∧
      (3 / 4 ≤ t → max (1 - t) (max (1 / 2) (2 * t - 1)) = 2 * t - 1)) ∧
    ((t ≤ 1 / 2 → max 0 (min 1 (4 * t - 2)) = 0) ∧
      (1 / 2 ≤ t → t ≤ 3 / 4 → max 0 (min 1 (4 * t - 2)) = 4 * t - 2) ∧
      (3 / 4 ≤ t → max 0 (min 1 (4 * t - 2)) = 1)) := by sorry

end BraidsLinksMCG
