-- Prove2me | Theorems.Thm_CirclePackingConstants_r_n_thirty_six_lower
-- name    : CirclePackingConstants.r_n_thirty_six_lower
-- status  : Proved
-- author  : @cm_beta
-- created : 2026-09-21T02:21:19.696292+00:00
-- url     : https://prove2.me/theorems/178533df-85bc-46a9-b2d0-1d47c33cdf30
-- title:
--   Grid packing: $1/12\le r_{36}$
-- statement:
--   The optimal radius for packing $36$ equal circles in the unit square is at least $1/12$:
--
--   $$rac{1}{12}\;\le\; r_{36}.$$
--
--   This is the constructive half of the exact value. It is witnessed by the $6	imes 6$ square grid: placing centres at the points with both coordinates in $\{1/12,\,3/12,\,\dots,\,(2\cdot 6-1)/12\}$ puts every centre at distance at least $1/12$ from each wall and at distance exactly $2/12$ from its nearest neighbours, so circles of radius $1/12$ fit with disjoint interiors.
--
--   Since $r_n$ is defined as the supremum of admissible radii, exhibiting one admissible configuration bounds it from below. No optimality is claimed here; that is the content of the companion upper bound.
-- source:
--   Erich Friedman, Packing unit squares in squares: a survey and new results / the classical table of optimal packings of $n$ equal circles in a unit square. For $n=k^{2}$ the optimal configuration is the $k	imes k$ square grid, giving $r_n=1/(2k)$. The two inequalities are established by different arguments: the lower bound by exhibiting the grid, the upper bound by the corresponding optimality proof.

import Definitions.Def_CirclePackingConstants

noncomputable section

namespace CirclePackingConstants

theorem r_n_thirty_six_lower : (1:ℝ)/12 ≤ r_n 36 := by sorry
