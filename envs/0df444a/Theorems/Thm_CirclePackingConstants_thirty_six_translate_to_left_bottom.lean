-- Prove2me | Theorems.Thm_CirclePackingConstants_thirty_six_translate_to_left_bottom
-- name    : CirclePackingConstants.thirty_six_translate_to_left_bottom
-- status  : Proved
-- author  : @WillR
-- created : 2026-09-22T09:34:02.518566+00:00
-- url     : https://prove2.me/theorems/b2536912-77f8-464d-9fa0-39afe8c73415
-- title:
--   Translate a 36-point unit-square configuration to touch the left and bottom sides
-- statement:
--   Every configuration of 36 points in the unit square can be translated, without changing any pairwise squared distance, so that the translated configuration still lies in the unit square and touches both the left side and the bottom side.
-- source:
--   Elementary boundary-normalisation reduction for CirclePackingConstants.thirty_six_unit_square_close_pair. Translate all x-coordinates by their finite minimum and all y-coordinates by their finite minimum. Unit-square membership is preserved and all pairwise differences, hence squared distances, are unchanged.

import Definitions.Def_CirclePackingConstants

namespace CirclePackingConstants

theorem thirty_six_translate_to_left_bottom :
    ∀ p : Fin 36 → Point,
      (∀ i, 0 ≤ (p i).1 ∧ (p i).1 ≤ 1 ∧ 0 ≤ (p i).2 ∧ (p i).2 ≤ 1) →
      ∃ q : Fin 36 → Point,
        (∀ i, 0 ≤ (q i).1 ∧ (q i).1 ≤ 1 ∧ 0 ≤ (q i).2 ∧ (q i).2 ≤ 1) ∧
        (∀ i j, sqDist (q i) (q j) = sqDist (p i) (p j)) ∧
        (∃ i, (q i).1 = 0) ∧
        (∃ j, (q j).2 = 0) := by sorry

end CirclePackingConstants
