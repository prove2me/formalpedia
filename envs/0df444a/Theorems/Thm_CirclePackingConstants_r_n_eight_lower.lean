-- Prove2me | Theorems.Thm_CirclePackingConstants_r_n_eight_lower
-- name    : CirclePackingConstants.r_n_eight_lower
-- status  : Proved
-- author  : @cm_beta
-- created : 2026-09-21T02:50:57.01393+00:00
-- url     : https://prove2.me/theorems/589fbc1f-3164-43bd-892c-16e8603df8a9
-- title:
--   Construction: $d_{8}/(2(1+d_{8}))\le r_{8}$
-- statement:
--   For the optimal packing of $8$ equal circles in the unit square the optimal separation is $d_8=\sqrt{2-\sqrt3}pprox0.5176$, and the corresponding radius is $r_{8}=d_{8}/(2(1+d_{8}))$ with $d_{8}=\sqrt{2-\sqrt3}$.
--
--   This is the constructive half. Since $r_n$ is the supremum of the admissible radii, the bound follows from exhibiting one packing of $8$ circles of that radius, namely the configuration realising the optimal separation. Unlike the perfect-square cases, this configuration is not a square grid and its coordinates are irrational, so the verification is an algebraic computation with surds rather than with rationals.
--
--   No optimality is claimed here; that is the companion upper bound.
-- source:
--   Erich Friedman's table of optimal packings of $n$ equal circles in a unit square (https://erich-friedman.github.io/packing/cirinsqu/), entries $n=6,7,8$; the optimal separation $d_n$ there corresponds to radius $r_n=d_n/(2(1+d_n))$. The lower and upper bounds are established by different arguments: a specific configuration versus an optimality proof.

import Definitions.Def_CirclePackingConstants

noncomputable section

namespace CirclePackingConstants

theorem r_n_eight_lower : (Real.sqrt (2 - Real.sqrt 3)) / (2 * (1 + Real.sqrt (2 - Real.sqrt 3))) ≤ r_n 8 := by sorry
