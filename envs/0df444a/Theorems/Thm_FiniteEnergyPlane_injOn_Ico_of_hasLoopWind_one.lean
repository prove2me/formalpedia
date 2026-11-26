-- Prove2me | Theorems.Thm_FiniteEnergyPlane_injOn_Ico_of_hasLoopWind_one
-- name    : FiniteEnergyPlane.injOn_Ico_of_hasLoopWind_one
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-11-26T21:43:45.339364+00:00
-- url     : https://prove2.me/theorems/bc416d03-4e80-5fdf-b161-f5593e270a7e
-- title:
--   Locally injective circle loops of degree one are injective
-- statement:
--   Let $\gamma : \mathbb{R} \to \mathbb{C}$ be a loop with `HasLoopWind γ 1` (continuous, $1$-periodic, nonvanishing, with a continuous argument $\theta$ satisfying $\theta(1) - \theta(0) = 2\pi$) and $|\gamma(t)| = 1$ for all $t$. Suppose every $t$ has a neighbourhood $(t-\varepsilon, t+\varepsilon)$ on which $\gamma$ is injective. Then $\gamma$ is injective on $[0, 1)$.
--
--   Role: turns local injectivity of a degree-one circle map into global injectivity on one period.
-- source:
--   Elementary lemma in the setting of U. Hryniewicz, Systems of global surfaces of section for dynamically convex Reeb flows on the 3-sphere, J. Symplectic Geom. 12 (2014), § 3.2

import Definitions.Def_FiniteEnergyPlane_Winding

namespace FiniteEnergyPlane

open Metric Set

/-- A locally injective loop on the unit circle with winding number `1` is injective on one period:
if `γ` is a `1`-periodic loop with `‖γ t‖ = 1` and winding number `1`, and every point has a
neighbourhood on which `γ` is injective, then `γ` is injective on `[0, 1)`. -/
theorem injOn_Ico_of_hasLoopWind_one (γ : ℝ → ℂ) (hγ : HasLoopWind γ 1) (h1 : ∀ t, ‖γ t‖ = 1)
    (hloc : ∀ t, ∃ ε > 0, InjOn γ (ball t ε)) : InjOn γ (Ico 0 1) := by
  sorry

end FiniteEnergyPlane
