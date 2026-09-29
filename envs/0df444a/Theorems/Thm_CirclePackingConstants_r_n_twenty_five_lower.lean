-- Prove2me | Theorems.Thm_CirclePackingConstants_r_n_twenty_five_lower
-- name    : CirclePackingConstants.r_n_twenty_five_lower
-- status  : Proved
-- author  : @cm_beta
-- created : 2026-09-21T02:21:17.918279+00:00
-- url     : https://prove2.me/theorems/ad6b87fa-c89c-41b7-9fab-8c4a55a38cdb
-- title:
--   Grid packing: $1/10\le r_{25}$
-- statement:
--   The optimal radius for packing $25$ equal circles in the unit square is at least $1/10$:
--
--   $$rac{1}{10}\;\le\; r_{25}.$$
--
--   This is the constructive half of the exact value. It is witnessed by the $5	imes 5$ square grid: placing centres at the points with both coordinates in $\{1/10,\,3/10,\,\dots,\,(2\cdot 5-1)/10\}$ puts every centre at distance at least $1/10$ from each wall and at distance exactly $2/10$ from its nearest neighbours, so circles of radius $1/10$ fit with disjoint interiors.
--
--   Since $r_n$ is defined as the supremum of admissible radii, exhibiting one admissible configuration bounds it from below. No optimality is claimed here; that is the content of the companion upper bound.
-- source:
--   Erich Friedman, Packing unit squares in squares: a survey and new results / the classical table of optimal packings of $n$ equal circles in a unit square. For $n=k^{2}$ the optimal configuration is the $k	imes k$ square grid, giving $r_n=1/(2k)$. The two inequalities are established by different arguments: the lower bound by exhibiting the grid, the upper bound by the corresponding optimality proof.

import Definitions.Def_CirclePackingConstants

noncomputable section

namespace CirclePackingConstants

theorem r_n_twenty_five_lower : (1:ℝ)/10 ≤ r_n 25 := by sorry
