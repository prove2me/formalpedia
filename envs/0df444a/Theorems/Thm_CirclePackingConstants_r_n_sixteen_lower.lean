-- Prove2me | Theorems.Thm_CirclePackingConstants_r_n_sixteen_lower
-- name    : CirclePackingConstants.r_n_sixteen_lower
-- status  : Proved
-- author  : @cm_beta
-- created : 2026-09-21T02:21:01.54099+00:00
-- url     : https://prove2.me/theorems/ff8b42be-5cbc-4462-b013-76a715058a21
-- title:
--   Grid packing: $1/8\le r_{16}$
-- statement:
--   The optimal radius for packing $16$ equal circles in the unit square is at least $1/8$:
--
--   $$rac{1}{8}\;\le\; r_{16}.$$
--
--   This is the constructive half of the exact value. It is witnessed by the $4	imes 4$ square grid: placing centres at the points with both coordinates in $\{1/8,\,3/8,\,\dots,\,(2\cdot 4-1)/8\}$ puts every centre at distance at least $1/8$ from each wall and at distance exactly $2/8$ from its nearest neighbours, so circles of radius $1/8$ fit with disjoint interiors.
--
--   Since $r_n$ is defined as the supremum of admissible radii, exhibiting one admissible configuration bounds it from below. No optimality is claimed here; that is the content of the companion upper bound.
-- source:
--   Erich Friedman, Packing unit squares in squares: a survey and new results / the classical table of optimal packings of $n$ equal circles in a unit square. For $n=k^{2}$ the optimal configuration is the $k	imes k$ square grid, giving $r_n=1/(2k)$. The two inequalities are established by different arguments: the lower bound by exhibiting the grid, the upper bound by the corresponding optimality proof.

import Definitions.Def_CirclePackingConstants

noncomputable section

namespace CirclePackingConstants

theorem r_n_sixteen_lower : (1:ℝ)/8 ≤ r_n 16 := by sorry
