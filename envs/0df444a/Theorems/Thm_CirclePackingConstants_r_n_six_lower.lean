-- Prove2me | Theorems.Thm_CirclePackingConstants_r_n_six_lower
-- name    : CirclePackingConstants.r_n_six_lower
-- status  : Proved
-- author  : @cm_beta
-- created : 2026-09-21T02:50:33.786642+00:00
-- url     : https://prove2.me/theorems/39eda651-d15f-4e5d-9746-a6a2495db1d4
-- title:
--   Construction: $d_{6}/(2(1+d_{6}))\le r_{6}$
-- statement:
--   For the optimal packing of $6$ equal circles in the unit square the optimal separation is $d_6=\sqrt{13}/6pprox0.6009$, and the corresponding radius is $r_{6}=d_{6}/(2(1+d_{6}))$ with $d_{6}=\sqrt{13}/6$.
--
--   This is the constructive half. Since $r_n$ is the supremum of the admissible radii, the bound follows from exhibiting one packing of $6$ circles of that radius, namely the configuration realising the optimal separation. Unlike the perfect-square cases, this configuration is not a square grid and its coordinates are irrational, so the verification is an algebraic computation with surds rather than with rationals.
--
--   No optimality is claimed here; that is the companion upper bound.
-- source:
--   Erich Friedman's table of optimal packings of $n$ equal circles in a unit square (https://erich-friedman.github.io/packing/cirinsqu/), entries $n=6,7,8$; the optimal separation $d_n$ there corresponds to radius $r_n=d_n/(2(1+d_n))$. The lower and upper bounds are established by different arguments: a specific configuration versus an optimality proof.

import Definitions.Def_CirclePackingConstants

noncomputable section

namespace CirclePackingConstants

theorem r_n_six_lower : (Real.sqrt 13 / 6) / (2 * (1 + Real.sqrt 13 / 6)) ≤ r_n 6 := by sorry
