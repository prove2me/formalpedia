-- Prove2me | Theorems.Thm_CirclePackingConstants_thirty_six_left_bottom_expand_to_three_sides
-- name    : CirclePackingConstants.thirty_six_left_bottom_expand_to_three_sides
-- status  : Proved
-- author  : @WillR
-- created : 2026-09-22T09:49:00.383834+00:00
-- url     : https://prove2.me/theorems/a9877114-199e-4ea0-a49b-095fdc4ef341
-- title:
--   Expand a nondegenerate left-bottom configuration until it touches a third side
-- statement:
--   A nondegenerate 36-point configuration in the unit square that touches the left and bottom sides can be uniformly expanded about the origin until it also touches the right or top side. The expansion stays in the unit square and never decreases any pairwise squared distance.
-- source:
--   Elementary normalisation. Let M be the larger of the maximum x-coordinate and maximum y-coordinate. Nondegeneracy gives M>0. Divide every coordinate by M. Since 0<M≤1, the new configuration remains in the unit square, retains the left/bottom contacts, touches right or top, and every pairwise squared distance is scaled by 1/M² ≥ 1.

import Definitions.Def_CirclePackingConstants

namespace CirclePackingConstants

theorem thirty_six_left_bottom_expand_to_three_sides :
    ∀ p : Fin 36 → Point,
      (∀ i, 0 ≤ (p i).1 ∧ (p i).1 ≤ 1 ∧ 0 ≤ (p i).2 ∧ (p i).2 ≤ 1) →
      (∃ i, (p i).1 = 0) →
      (∃ j, (p j).2 = 0) →
      (∃ k, (p k).1 ≠ 0 ∨ (p k).2 ≠ 0) →
      ∃ q : Fin 36 → Point,
        (∀ i, 0 ≤ (q i).1 ∧ (q i).1 ≤ 1 ∧ 0 ≤ (q i).2 ∧ (q i).2 ≤ 1) ∧
        (∀ i j, sqDist (p i) (p j) ≤ sqDist (q i) (q j)) ∧
        (∃ i, (q i).1 = 0) ∧
        (∃ j, (q j).2 = 0) ∧
        ((∃ i, (q i).1 = 1) ∨ (∃ j, (q j).2 = 1)) := by sorry

end CirclePackingConstants
