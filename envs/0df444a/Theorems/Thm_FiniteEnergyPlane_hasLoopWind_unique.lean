-- Prove2me | Theorems.Thm_FiniteEnergyPlane_hasLoopWind_unique
-- name    : FiniteEnergyPlane.hasLoopWind_unique
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-11-01T22:36:26.201845+00:00
-- url     : https://prove2.me/theorems/c1ea0def-b893-4a37-a283-ffbd6e4afe1a
-- title:
--   The winding number of a loop in the punctured plane is unique
-- statement:
--   Let $f:\mathbb{R}\to\mathbb{C}\setminus\{0\}$ be a continuous $1$-periodic loop. If $f$ has winding number $k$ and winding number $k'$, then $k=k'$.
--
--   Here "$f$ has winding number $k$" means: there is a continuous $\theta:\mathbb{R}\to\mathbb{R}$ with $f(t)=|f(t)|e^{i\theta(t)}$ for all $t$ and $\theta(1)-\theta(0)=2\pi k$. The statement says this integer does not depend on the choice of $\theta$, so the winding number is well defined.
--
--   **Formalization Note** "$f$ has winding number $k$" is `HasLoopWind f k` (`FiniteEnergyPlane_Winding`); the conclusion is `k = k'`.
-- source:
--   Standard topology of the circle; used in C. Wendl, Lectures on Symplectic Field Theory (2026 notes), arXiv:1612.01009, Section 3.7; H. Hofer, K. Wysocki, E. Zehnder, GAFA 5 (1995), Section 3.

import Definitions.Def_FiniteEnergyPlane_Winding

namespace FiniteEnergyPlane

/-- The winding number of a loop in `ℂ \ {0}` is unique. -/
theorem hasLoopWind_unique {f : ℝ → ℂ} {k k' : ℤ} (h : HasLoopWind f k)
    (h' : HasLoopWind f k') : k = k' := by
  sorry

end FiniteEnergyPlane
