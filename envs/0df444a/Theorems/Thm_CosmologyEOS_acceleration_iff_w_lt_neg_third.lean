-- Prove2me | Theorems.Thm_CosmologyEOS_acceleration_iff_w_lt_neg_third
-- name    : CosmologyEOS.acceleration_iff_w_lt_neg_third
-- status  : Open
-- author  : @Lucas
-- created : 2026-10-09T21:34:59.650062+00:00
-- url     : https://prove2.me/theorems/c979e2ca-c716-4ec8-85c8-29c245f9a90d
-- title:
--   Accelerated expansion iff $w < -1/3$
-- statement:
--   Let $G>0$ and $w$ be real, and let $a,\varepsilon,p$ be real functions of time. At a time $t$ suppose $a(t)>0$, $\varepsilon(t)>0$, $p(t) = w\,\varepsilon(t)$, and the acceleration equation with $\Lambda = 0$ holds: $3\frac{\ddot a}{a} = -4\pi G(\varepsilon + 3p)$. Then
--
--   $$\ddot a(t) > 0 \iff w < -\tfrac13.$$
--
--   This is the source's statement that the expansion of the universe is accelerating for any equation of state $w<-1/3$ (the fluid itself playing the role of dark energy).
--
--   **Formalization Note** The cosmological constant is set to $0$ here because a nonzero $\Lambda$ is itself a $w=-1$ component; the source's criterion refers to the total equation of state.
-- source:
--   Wikipedia, "Equation of state (cosmology)", revision 1375011367, https://en.wikipedia.org/w/index.php?title=Equation_of_state_(cosmology)&oldid=1375011367, section 'Acceleration of cosmic inflation'

import Mathlib
import Definitions.Def_CosmologyEOS_Defs

open Real Filter Topology

namespace CosmologyEOS

theorem acceleration_iff_w_lt_neg_third (G w : ℝ) (hG : 0 < G) (a ε p : ℝ → ℝ) (t : ℝ)
    (ha : 0 < a t) (hε : 0 < ε t) (heos : p t = w * ε t)
    (hacc : AccelerationEquation G 0 a ε p t) :
    0 < deriv (deriv a) t ↔ w < -1 / 3 := by
  sorry

end CosmologyEOS
