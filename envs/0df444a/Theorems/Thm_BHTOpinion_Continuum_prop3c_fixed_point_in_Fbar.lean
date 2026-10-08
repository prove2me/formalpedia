-- Prove2me | Theorems.Thm_BHTOpinion_Continuum_prop3c_fixed_point_in_Fbar
-- name    : BHTOpinion.Continuum.prop3c_fixed_point_in_Fbar
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T06:40:55.499244+00:00
-- url     : https://prove2.me/theorems/979af101-33d7-404f-b3e9-78d6bdcf407f
-- title:
--   Proposition 3(c) — every nondecreasing fixed point lies in F̄
-- statement:
--   Let $\tilde s$ be a nondecreasing function on $I=[0,1]$ that is a fixed point of the continuum model, i.e. (3.2) with initial condition $\tilde s$ has the unique solution $x_t=\tilde s$. Then
--
--   $$\tilde s\in\bar F:$$
--
--   for almost every pair $(\alpha,\beta)\in I^2$, either $\tilde s(\alpha)=\tilde s(\beta)$ or $|\tilde s(\alpha)-\tilde s(\beta)|\ge 1$.
--
--   With part (b), this sandwiches the set of nondecreasing fixed points between $F$ and $\bar F$.
-- source:
--   Blondel, Hendrickx, Tsitsiklis, SIAM J. Control Optim. 48 (2010), Proposition 3(c), p. 5227

import Mathlib
import Definitions.Def_BHTOpinion_Continuum_Model

open MeasureTheory Filter Topology

namespace BHTOpinion.Continuum

theorem prop3c_fixed_point_in_Fbar (s : ℝ → ℝ) (hs : InX s) (hfix : IsFixedPoint s) :
    InFbar s := by sorry

end BHTOpinion.Continuum
