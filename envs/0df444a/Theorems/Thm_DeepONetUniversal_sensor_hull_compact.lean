-- Prove2me | Theorems.Thm_DeepONetUniversal_sensor_hull_compact
-- name    : DeepONetUniversal.sensor_hull_compact
-- status  : Open
-- author  : @Xeroth
-- created : 2026-11-24T08:36:37.779258+00:00
-- url     : https://prove2.me/theorems/a81ef35b-9990-4e94-baae-b29bc08a38a7
-- title:
--   Lemma 7: W is compact
-- statement:
--   Let $a<b$ and let $V$ be a compact subset of $C[a,b]$. With $U_m=\{\mathcal L_m(u):u\in V\}$ the set of piecewise-linear interpolants at the $m+1$ uniform sensors and $W_m=V\cup U_m$, the set
--
--   $$W=\bigcup_{i=1}^\infty W_i$$
--
--   is compact in $C[a,b]$.
--
--   Theorem 2 needs the ODE operator $G$ and the Lipschitz condition on $W$, which contains both the inputs and all their interpolants.
-- source:
--   Lu, Jin and Karniadakis, DeepONet: Learning nonlinear operators for identifying differential equations based on the universal approximation theorem of operators, arXiv:1910.03193v3 (2019), Section 3, p. 6, and Appendix B, Lemma 7, p. 20

import Mathlib
import Definitions.Def_DeepONetUniversal_Basic

open MeasureTheory Filter Topology

namespace DeepONetUniversal

theorem sensor_hull_compact {a b : ℝ} (hab : a < b) (V : Set C(Set.Icc a b, ℝ))
    (hV : IsCompact V) :
    IsCompact (sensorHull a b V) := by sorry

end DeepONetUniversal
