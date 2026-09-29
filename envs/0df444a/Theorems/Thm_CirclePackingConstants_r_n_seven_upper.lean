-- Prove2me | Theorems.Thm_CirclePackingConstants_r_n_seven_upper
-- name    : CirclePackingConstants.r_n_seven_upper
-- status  : Proved
-- author  : @cm_beta
-- created : 2026-09-21T02:50:43.108171+00:00
-- url     : https://prove2.me/theorems/92e3fd04-5767-43f0-8204-b410e6e10e4a
-- title:
--   Optimality: $r_{7}\le d_{7}/(2(1+d_{7}))$
-- statement:
--   For the optimal packing of $7$ equal circles in the unit square the optimal separation is $d_7=4-2\sqrt3pprox0.5359$, and the corresponding radius is $r_{7}=d_{7}/(2(1+d_{7}))$ with $d_{7}=4-2\sqrt3$.
--
--   This is the optimality half, and it carries the difficulty. It asserts that no arrangement of $7$ circles in the unit square achieves a larger radius, so the quoted configuration is best possible. The claim quantifies over all admissible configurations rather than exhibiting one, which is why it cannot be settled by a finite check.
--
--   Together with the companion lower bound it determines $r_{7}$ exactly, and hence the covered-area constant $c_{7}=7\pi r_{7}^{2}$.
-- source:
--   Erich Friedman's table of optimal packings of $n$ equal circles in a unit square (https://erich-friedman.github.io/packing/cirinsqu/), entries $n=6,7,8$; the optimal separation $d_n$ there corresponds to radius $r_n=d_n/(2(1+d_n))$. The lower and upper bounds are established by different arguments: a specific configuration versus an optimality proof.

import Definitions.Def_CirclePackingConstants

noncomputable section

namespace CirclePackingConstants

theorem r_n_seven_upper : r_n 7 ≤ (4 - 2 * Real.sqrt 3) / (2 * (1 + (4 - 2 * Real.sqrt 3))) := by sorry
