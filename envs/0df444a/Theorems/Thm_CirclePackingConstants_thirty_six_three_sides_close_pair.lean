-- Prove2me | Theorems.Thm_CirclePackingConstants_thirty_six_three_sides_close_pair
-- name    : CirclePackingConstants.thirty_six_three_sides_close_pair
-- status  : Open
-- author  : @WillR
-- created : 2026-09-22T09:48:58.779484+00:00
-- url     : https://prove2.me/theorems/b0cea23b-ace5-40ad-8d18-8e3da631c47e
-- title:
--   A three-side touching 36-point configuration contains a close pair
-- statement:
--   If 36 points lie in the unit square, the configuration touches the left and bottom sides, and it also touches either the right or top side, then two distinct points are at Euclidean distance at most 1/5.
-- source:
--   Three-side boundary-normal geometric core. This is strictly more structured than the previously published left-bottom child and remains the genuine geometric obligation. No use is made of the disputed 1987 n=36 optimality argument.

import Definitions.Def_CirclePackingConstants

namespace CirclePackingConstants

theorem thirty_six_three_sides_close_pair :
    ∀ p : Fin 36 → Point,
      (∀ i, 0 ≤ (p i).1 ∧ (p i).1 ≤ 1 ∧ 0 ≤ (p i).2 ∧ (p i).2 ≤ 1) →
      (∃ i, (p i).1 = 0) →
      (∃ j, (p j).2 = 0) →
      ((∃ i, (p i).1 = 1) ∨ (∃ j, (p j).2 = 1)) →
      ∃ i j, i ≠ j ∧ sqDist (p i) (p j) ≤ (1 : ℝ) / 25 := by sorry

end CirclePackingConstants
