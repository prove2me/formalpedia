-- Prove2me | Theorems.Thm_CirclePackingConstants_r_n_six_upper
-- name    : CirclePackingConstants.r_n_six_upper
-- status  : Proved
-- author  : @cm_beta
-- created : 2026-09-21T02:50:30.990584+00:00
-- url     : https://prove2.me/theorems/e6b22b53-ef66-4d55-9896-03633a6f57cf
-- title:
--   Optimality: $r_{6}\le d_{6}/(2(1+d_{6}))$
-- statement:
--   For the optimal packing of $6$ equal circles in the unit square the optimal separation is $d_6=\sqrt{13}/6pprox0.6009$, and the corresponding radius is $r_{6}=d_{6}/(2(1+d_{6}))$ with $d_{6}=\sqrt{13}/6$.
--
--   This is the optimality half, and it carries the difficulty. It asserts that no arrangement of $6$ circles in the unit square achieves a larger radius, so the quoted configuration is best possible. The claim quantifies over all admissible configurations rather than exhibiting one, which is why it cannot be settled by a finite check.
--
--   Together with the companion lower bound it determines $r_{6}$ exactly, and hence the covered-area constant $c_{6}=6\pi r_{6}^{2}$.
-- source:
--   Erich Friedman's table of optimal packings of $n$ equal circles in a unit square (https://erich-friedman.github.io/packing/cirinsqu/), entries $n=6,7,8$; the optimal separation $d_n$ there corresponds to radius $r_n=d_n/(2(1+d_n))$. The lower and upper bounds are established by different arguments: a specific configuration versus an optimality proof.

import Definitions.Def_CirclePackingConstants

noncomputable section

namespace CirclePackingConstants

theorem r_n_six_upper : r_n 6 ≤ (Real.sqrt 13 / 6) / (2 * (1 + Real.sqrt 13 / 6)) := by sorry
