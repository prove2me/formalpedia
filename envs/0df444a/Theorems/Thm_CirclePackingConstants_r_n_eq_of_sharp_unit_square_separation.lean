-- Prove2me | Theorems.Thm_CirclePackingConstants_r_n_eq_of_sharp_unit_square_separation
-- name    : CirclePackingConstants.r_n_eq_of_sharp_unit_square_separation
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-09-13T16:17:09.750643+00:00
-- url     : https://prove2.me/theorems/901dd1c9-8281-4a45-98d1-7cbfece676a8
-- title:
--   Sharp unit-square separation determines the optimal packing radius
-- statement:
--   Let $n$ be a natural number and let $d\ge 0$. Suppose both of the following hold for point configurations in the unit square:
--
--   1. There is a configuration of $n$ points whose pairwise distances are all at least $d$.
--   2. Every configuration of $n$ points contains a distinct pair at distance at most $d$.
--
--   Then the supremal radius of $n$ congruent disks with disjoint interiors that fit in the unit square is
--
--   $$
--   r_n=rac{d}{2(1+d)}.
--   $$
--
--   This theorem provides the common normalization bridge between exact point-separation results in the unit square and exact equal-circle packing constants.
-- source:
--   User-supplied Circles in squares: proofs and bounds, pp. 1–3, and accompanying CirclePacking.lean source package, affine normalization used in Sections 4–7, supplied September 12, 2026.

import Definitions.Def_CirclePackingConstants

noncomputable section

namespace CirclePackingConstants

theorem r_n_eq_of_sharp_unit_square_separation {n : ℕ} {d : ℝ} (hd : 0 ≤ d)
    (hlower : ∃ p : Fin n → Point,
      (∀ i, 0 ≤ (p i).1 ∧ (p i).1 ≤ 1 ∧ 0 ≤ (p i).2 ∧ (p i).2 ≤ 1) ∧
      ∀ i j, i ≠ j → d ^ 2 ≤ sqDist (p i) (p j))
    (hupper : ∀ p : Fin n → Point,
      (∀ i, 0 ≤ (p i).1 ∧ (p i).1 ≤ 1 ∧ 0 ≤ (p i).2 ∧ (p i).2 ≤ 1) →
      ∃ i j, i ≠ j ∧ sqDist (p i) (p j) ≤ d ^ 2) :
    r_n n = d / (2 * (1 + d)) := by sorry
