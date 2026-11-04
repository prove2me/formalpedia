-- Prove2me | Theorems.Thm_FiniteEnergyPlane_hasLoopWind_comp_add
-- name    : FiniteEnergyPlane.hasLoopWind_comp_add
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-11-03T10:04:42.24222+00:00
-- url     : https://prove2.me/theorems/19e49196-274e-4f80-9323-50787feb6dc9
-- title:
--   Winding numbers of loops are invariant under a shift of the parameter
-- statement:
--   Let $f:\mathbb{R}\to\mathbb{C}\setminus\{0\}$ be a continuous $1$-periodic loop with winding number $k\in\mathbb{Z}$, and let $d\in\mathbb{R}$. Then the shifted loop $t\mapsto f(t+d)$ also has winding number $k$.
--
--   This lets a winding number be read off a reparametrized loop, for example when an asymptotic description of a curve end involves a constant phase shift.
--
--   **Formalization Note** "Winding number $k$" is `HasLoopWind f k`: $f$ is continuous, $1$-periodic and never $0$, and some continuous $\theta$ with $f(t)=|f(t)|e^{i\theta(t)}$ has $\theta(1)-\theta(0)=2\pi k$.
-- source:
--   Standard fact on winding numbers of loops in $\mathbb{C}\setminus\{0\}$; used in U. Hryniewicz, J. Symplectic Geom. 12 (2014), arXiv:1105.2077, Section 2.2.4

import Definitions.Def_FiniteEnergyPlane_Winding

namespace FiniteEnergyPlane

/-- The winding number of a loop in `ℂ \ {0}` is unchanged by a shift `t ↦ t + d` of its
parameter. -/
theorem hasLoopWind_comp_add {f : ℝ → ℂ} {k : ℤ} (hf : HasLoopWind f k) (d : ℝ) :
    HasLoopWind (fun t => f (t + d)) k := by
  sorry

end FiniteEnergyPlane
