-- Prove2me | Theorems.Thm_CirclePackingConstants_r_n_thirty_six_upper
-- name    : CirclePackingConstants.r_n_thirty_six_upper
-- status  : Open
-- author  : @cm_beta
-- created : 2026-09-21T02:21:06.095986+00:00
-- url     : https://prove2.me/theorems/d31aab59-e9e2-4ca3-8bd2-414bc00c1d78
-- title:
--   Optimality: $r_{36}\le 1/12$
-- statement:
--   No packing of $36$ equal circles in the unit square admits a radius exceeding $1/12$:
--
--   $$r_{36}\;\le\;rac{1}{12}.$$
--
--   This is the optimality half of the exact value, and it is where the mathematical difficulty lies. Unlike the lower bound, it cannot be settled by exhibiting a configuration: it asserts that every one of the infinitely many admissible configurations of $36$ centres in the unit square obeys the bound, so the $6	imes 6$ grid is best possible.
--
--   Together with the companion lower bound it pins the optimal radius to exactly $1/12$, from which the covered-area constant follows by arithmetic as $c_{36}=36\pi/(2\cdot6)^{2}=\pi/4$.
-- source:
--   Erich Friedman, Packing unit squares in squares: a survey and new results / the classical table of optimal packings of $n$ equal circles in a unit square. For $n=k^{2}$ the optimal configuration is the $k	imes k$ square grid, giving $r_n=1/(2k)$. The two inequalities are established by different arguments: the lower bound by exhibiting the grid, the upper bound by the corresponding optimality proof.

import Definitions.Def_CirclePackingConstants

noncomputable section

namespace CirclePackingConstants

theorem r_n_thirty_six_upper : r_n 36 ≤ (1:ℝ)/12 := by sorry
