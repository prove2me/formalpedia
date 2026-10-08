-- Prove2me | Theorems.Thm_CirclePackingConstants_r_n_eight_upper
-- name    : CirclePackingConstants.r_n_eight_upper
-- status  : Proved
-- author  : @cm_beta
-- created : 2026-09-21T02:50:37.853103+00:00
-- url     : https://prove2.me/theorems/62c53c90-a9bf-4b0c-b87a-8751d7909cad
-- title:
--   Optimality: $r_{8}\le d_{8}/(2(1+d_{8}))$
-- statement:
--   For the optimal packing of $8$ equal circles in the unit square the optimal separation is $d_8=\sqrt{2-\sqrt3}pprox0.5176$, and the corresponding radius is $r_{8}=d_{8}/(2(1+d_{8}))$ with $d_{8}=\sqrt{2-\sqrt3}$.
--
--   This is the optimality half, and it carries the difficulty. It asserts that no arrangement of $8$ circles in the unit square achieves a larger radius, so the quoted configuration is best possible. The claim quantifies over all admissible configurations rather than exhibiting one, which is why it cannot be settled by a finite check.
--
--   Together with the companion lower bound it determines $r_{8}$ exactly, and hence the covered-area constant $c_{8}=8\pi r_{8}^{2}$.
-- source:
--   Erich Friedman's table of optimal packings of $n$ equal circles in a unit square (https://erich-friedman.github.io/packing/cirinsqu/), entries $n=6,7,8$; the optimal separation $d_n$ there corresponds to radius $r_n=d_n/(2(1+d_n))$. The lower and upper bounds are established by different arguments: a specific configuration versus an optimality proof.

import Definitions.Def_CirclePackingConstants

noncomputable section

namespace CirclePackingConstants

theorem r_n_eight_upper : r_n 8 ≤ (Real.sqrt (2 - Real.sqrt 3)) / (2 * (1 + Real.sqrt (2 - Real.sqrt 3))) := by sorry
