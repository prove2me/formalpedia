-- Prove2me | Theorems.Thm_BraidsLinksMCG_adjacentRadialProfileFormulas_child_v1
-- name    : BraidsLinksMCG.adjacentRadialProfileFormulas_child_v1
-- status  : Open
-- author  : @WillR
-- created : 2026-09-23T22:44:43.426166+00:00
-- url     : https://prove2.me/theorems/21c8da0f-b82a-40ce-8dd5-5b99d9898d5a
-- title:
--   The adjacent radial radius and turn profiles are piecewise elementary
-- statement:
--   On the unit interval, the radius and angular-turn functions used in the adjacent radial/profile path have the exact three-piece formulas before, during, and after the half-turn. These scalar identities isolate the parametrization calculation used by the adjacent lollipop path.
-- source:
--   The definitions and breakpoints are taken verbatim from the adjacent radial/profile path construction in adjacent_candidate_work_v28.lean; the radius and turn formulas are the scalar source lemmas used on its first, middle, and final thirds.

import Mathlib

namespace BraidsLinksMCG

noncomputable def adjacentRadius (t : ℝ) : ℝ := max (1 - t) (max (1 / 2) (2 * t - 1))

noncomputable def adjacentTurn (t : ℝ) : ℝ := max 0 (min 1 (4 * t - 2))

theorem adjacentRadialProfileFormulas_child_v1 (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    ((t ≤ 1 / 2 → adjacentRadius t = 1 - t) ∧
      (1 / 2 ≤ t → t ≤ 3 / 4 → adjacentRadius t = 1 / 2) ∧
      (3 / 4 ≤ t → adjacentRadius t = 2 * t - 1)) ∧
    ((t ≤ 1 / 2 → adjacentTurn t = 0) ∧
      (1 / 2 ≤ t → t ≤ 3 / 4 → adjacentTurn t = 4 * t - 2) ∧
      (3 / 4 ≤ t → adjacentTurn t = 1)) := by sorry

end BraidsLinksMCG
