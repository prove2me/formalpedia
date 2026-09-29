-- Prove2me | Theorems.Thm_CirclePackingConstants_thirty_six_left_bottom_close_pair
-- name    : CirclePackingConstants.thirty_six_left_bottom_close_pair
-- status  : Open
-- author  : @WillR
-- created : 2026-09-22T09:33:49.946783+00:00
-- url     : https://prove2.me/theorems/bdf250ac-6823-48c8-afaf-3c085fd9fe30
-- title:
--   A left-and-bottom touching 36-point configuration contains a close pair
-- statement:
--   If 36 points lie in the unit square and the configuration touches both the left side and the bottom side, then two distinct points are at Euclidean distance at most 1/5.
-- source:
--   Boundary-normal geometric core obtained from CirclePackingConstants.thirty_six_unit_square_close_pair by translation invariance. This remains the genuine hard geometric obligation; no use is made of the disputed Kirchner-Wengerodt optimality argument.

import Definitions.Def_CirclePackingConstants

namespace CirclePackingConstants

theorem thirty_six_left_bottom_close_pair :
    ∀ p : Fin 36 → Point,
      (∀ i, 0 ≤ (p i).1 ∧ (p i).1 ≤ 1 ∧ 0 ≤ (p i).2 ∧ (p i).2 ≤ 1) →
      (∃ i, (p i).1 = 0) →
      (∃ j, (p j).2 = 0) →
      ∃ i j, i ≠ j ∧ sqDist (p i) (p j) ≤ (1 : ℝ) / 25 := by sorry

end CirclePackingConstants
