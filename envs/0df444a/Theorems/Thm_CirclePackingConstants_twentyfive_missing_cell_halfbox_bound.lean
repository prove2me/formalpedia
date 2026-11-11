-- Prove2me | Theorems.Thm_CirclePackingConstants_twentyfive_missing_cell_halfbox_bound
-- name    : CirclePackingConstants.twentyfive_missing_cell_halfbox_bound
-- status  : Open
-- author  : @parclytaxel
-- created : 2026-11-10T17:58:46.143349+00:00
-- url     : https://prove2.me/theorems/8fb934b7-bfe0-4ddf-934a-1fc9b9479ccd
-- title:
--   A separated half-cell packing with an empty fifth-cell has at most 24 points
-- statement:
--   Divide each cell of the $5\times5$ subdivision of the unit square into its lower and upper halves. The resulting fifty closed rectangles are
--
--   $$R_{a,b,e}=[a/5,(a+1)/5]\times[b/5+e/10,b/5+(e+1)/10],$$
--
--   where $a,b\in\{0,1,2,3,4\}$ and $e\in\{0,1\}$. Let $S$ be any set of these half-cell indices, and choose one point $q_r\in R_r$ for each $r\in S$. Suppose the chosen points have pairwise squared distances strictly greater than $1/16$. If there is a full fifth-cell whose two half-cell indices both lie outside $S$, then
--
--   $$|S|\le24.$$
--
--   This is a proposed geometric subproblem for the twenty-five-point occupancy theorem. It concerns assigned half-cell indices: a point on a rectangle boundary may belong geometrically to another rectangle, and no exclusion from that rectangle is assumed. The values of $q$ outside $S$ are unrestricted.
--
--   The half-cell diagonal has square $1/20<1/16$, so every separated configuration can be encoded using at most one point in each of these fifty rectangles. The statement isolates the remaining global obstruction after that elementary local bound. It does not assert that the obstruction has already been proved or that checking only the fifty original rectangles suffices to certify it; further geometric estimates or subdivision are needed.
-- source:
--   Original auxiliary half-cell cardinality lemma proposed for CirclePackingConstants.twentyfive_cell_occupancy. Classical context: G. Wengerodt, Die dichteste Packung von 25 Kreisen in einem Quadrat, Ann. Univ. Sci. Budapest. Eotvos Sect. Math. 30 (1987), 3-15. The half-cell formulation is proposed here, not quoted from that paper.

import Definitions.Def_CirclePackingConstants

noncomputable section

namespace CirclePackingConstants

theorem twentyfive_missing_cell_halfbox_bound
    (S : Finset ((Fin 5 × Fin 5) × Fin 2))
    (q : ((Fin 5 × Fin 5) × Fin 2) → Point)
    (hc : ∀ r ∈ S,
      ((r.1.1.val : ℝ) / 5 ≤ (q r).1 ∧
       (q r).1 ≤ ((r.1.1.val : ℝ) + 1) / 5) ∧
      ((r.1.2.val : ℝ) / 5 + (r.2.val : ℝ) / 10 ≤ (q r).2 ∧
       (q r).2 ≤ (r.1.2.val : ℝ) / 5 + ((r.2.val : ℝ) + 1) / 10))
    (hd : ∀ r ∈ S, ∀ t ∈ S, r ≠ t → (1 : ℝ) / 16 < sqDist (q r) (q t))
    (hempty : ∃ c : Fin 5 × Fin 5, ∀ b : Fin 2, (c, b) ∉ S) :
    S.card ≤ 24 := by sorry
