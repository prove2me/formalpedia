-- Prove2me | Theorems.Thm_FiniteEnergyPlane_exists_hasLoopWind
-- name    : FiniteEnergyPlane.exists_hasLoopWind
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-11-01T20:35:17.609272+00:00
-- url     : https://prove2.me/theorems/844e9de6-ea30-445b-9834-e3ceb4446cb4
-- title:
--   Continuous periodic loops in $\mathbb{C}\setminus\{0\}$ have a winding number
-- statement:
--   Let $f:\mathbb{R}\to\mathbb{C}$ be continuous, $1$-periodic and nowhere zero. Then $f$ has an integer winding number $k$: there is a continuous $\theta:\mathbb{R}\to\mathbb{R}$ with $f(t)=|f(t)|e^{i\theta(t)}$ for all $t\in\mathbb{R}$ and $\theta(1)-\theta(0)=2\pi k$.
--
--   This is the basic existence statement for the winding invariant `HasLoopWind` used throughout the winding-number milestones of finite-energy planes.
--
--   **Formalization Note** The conclusion is `∃ k : ℤ, HasLoopWind f k` with `HasLoopWind` from `FiniteEnergyPlane_Winding`; the angle function $\theta$ is required on all of $\mathbb{R}$, not only on $[0,1]$.
-- source:
--   C. Wendl, Lectures on Symplectic Field Theory (2026 notes), arXiv:1612.01009, Section 3.7 (winding numbers of loops in C minus 0); standard.

import Definitions.Def_FiniteEnergyPlane_Winding

namespace FiniteEnergyPlane

/-- A continuous `1`-periodic loop in `ℂ \ {0}` has a winding number. -/
theorem exists_hasLoopWind (f : ℝ → ℂ) (hf : Continuous f) (hper : Function.Periodic f 1)
    (h0 : ∀ t, f t ≠ 0) : ∃ k : ℤ, HasLoopWind f k := by
  sorry

end FiniteEnergyPlane
