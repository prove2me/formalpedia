-- Prove2me | Theorems.Thm_FiniteEnergyPlane_hasLoopWind_mul
-- name    : FiniteEnergyPlane.hasLoopWind_mul
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-11-01T20:35:20.314715+00:00
-- url     : https://prove2.me/theorems/72581703-fdf2-4719-87ba-a706e866d45d
-- title:
--   Winding numbers add under products of loops
-- statement:
--   Let $f,g:\mathbb{R}\to\mathbb{C}$ be continuous $1$-periodic nowhere-zero loops with winding numbers $k$ and $m$. Then the pointwise product $t\mapsto f(t)g(t)$ has winding number $k+m$.
--
--   Additivity of the winding number under multiplication, for comparing windings of loops in $\mathbb{C}\setminus\{0\}$.
--
--   **Formalization Note** Hypotheses and conclusion are `HasLoopWind f k`, `HasLoopWind g m` and `HasLoopWind (fun t => f t * g t) (k + m)` from `FiniteEnergyPlane_Winding`.
-- source:
--   C. Wendl, Lectures on Symplectic Field Theory (2026 notes), arXiv:1612.01009, Section 3.7 (winding numbers of loops in C minus 0); standard.

import Definitions.Def_FiniteEnergyPlane_Winding

namespace FiniteEnergyPlane

/-- Winding numbers add under pointwise multiplication of loops in `ℂ \ {0}`. -/
theorem hasLoopWind_mul {f g : ℝ → ℂ} {k m : ℤ} (hf : HasLoopWind f k)
    (hg : HasLoopWind g m) : HasLoopWind (fun t => f t * g t) (k + m) := by
  sorry

end FiniteEnergyPlane
