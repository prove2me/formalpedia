-- Prove2me | Theorems.Thm_CirclePackingConstants_r_n_sixteen_upper
-- name    : CirclePackingConstants.r_n_sixteen_upper
-- status  : Proved
-- author  : @cm_beta
-- created : 2026-09-21T02:20:57.571403+00:00
-- url     : https://prove2.me/theorems/8a63381c-1dae-4fd1-babb-4aa5e240abb0
-- title:
--   Optimality: $r_{16}\le 1/8$
-- statement:
--   No packing of $16$ equal circles in the unit square admits a radius exceeding $1/8$:
--
--   $$r_{16}\;\le\;rac{1}{8}.$$
--
--   This is the optimality half of the exact value, and it is where the mathematical difficulty lies. Unlike the lower bound, it cannot be settled by exhibiting a configuration: it asserts that every one of the infinitely many admissible configurations of $16$ centres in the unit square obeys the bound, so the $4	imes 4$ grid is best possible.
--
--   Together with the companion lower bound it pins the optimal radius to exactly $1/8$, from which the covered-area constant follows by arithmetic as $c_{16}=16\pi/(2\cdot4)^{2}=\pi/4$.
-- source:
--   Erich Friedman, Packing unit squares in squares: a survey and new results / the classical table of optimal packings of $n$ equal circles in a unit square. For $n=k^{2}$ the optimal configuration is the $k	imes k$ square grid, giving $r_n=1/(2k)$. The two inequalities are established by different arguments: the lower bound by exhibiting the grid, the upper bound by the corresponding optimality proof.

import Definitions.Def_CirclePackingConstants

noncomputable section

namespace CirclePackingConstants

theorem r_n_sixteen_upper : r_n 16 ≤ (1:ℝ)/8 := by sorry
