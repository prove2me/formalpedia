-- Prove2me | Theorems.Thm_CirclePackingConstants_six_unit_square_close_pair
-- name    : CirclePackingConstants.six_unit_square_close_pair
-- status  : Proved
-- author  : @WillR
-- created : 2026-09-22T00:07:22.182985+00:00
-- url     : https://prove2.me/theorems/e5b0961f-14a9-4351-9ab8-8418a6b3d2a4
-- title:
--   Six points in the unit square contain a close pair
-- statement:
--   Let $p_0,\dots,p_5$ be six points in the unit square $[0,1]^2$. Then there exist distinct indices $i \neq j$ with squared Euclidean distance at most $13/36$, i.e. $|p_i-p_j| \le \sqrt{13}/6$.
--
--   This is the point-separation form of the optimality of the six-circle packing: $d_6 = \sqrt{13}/6$ is the largest separation attainable by six points in the unit square, so no configuration avoids a pair at distance at most $d_6$. Combined with the matching six-point configuration attaining $13/36$, it determines the optimal radius $r_6 = d_6/(2(1+d_6))$.
--
--   **Formalization Note** Lean formalizes points as $\mathbb{R} \times \mathbb{R}$ via `CirclePackingConstants.Point` and squared distance via `CirclePackingConstants.sqDist`.
-- source:
--   Erich Friedman's table of optimal packings of $n$ equal circles in a unit square (https://erich-friedman.github.io/packing/cirinsqu/), entry $n=6$; the optimal separation $d_6=\sqrt{13}/6$ and the point-separation optimality half used in Sections 4-7 of the supplied Circles in squares source package.

import Definitions.Def_CirclePackingConstants

namespace CirclePackingConstants

theorem six_unit_square_close_pair : ∀ p : Fin 6 → Point, (∀ i, 0 ≤ (p i).1 ∧ (p i).1 ≤ 1 ∧ 0 ≤ (p i).2 ∧ (p i).2 ≤ 1) → ∃ i j, i ≠ j ∧ sqDist (p i) (p j) ≤ (13 : ℝ) / 36 := by sorry

end CirclePackingConstants
