-- Prove2me | Theorems.Thm_FiniteEnergyPlane_hasLoopWind_zero_of_forall_ne_ray
-- name    : FiniteEnergyPlane.hasLoopWind_zero_of_forall_ne_ray
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-11-01T20:35:23.754843+00:00
-- url     : https://prove2.me/theorems/f3dc43f7-1e07-4ca8-992a-f0c8a914a7c5
-- title:
--   A loop missing a ray from the origin has winding number zero
-- statement:
--   Let $q:\mathbb{R}\to\mathbb{C}$ be continuous and $1$-periodic, and let $w\in\mathbb{C}\setminus\{0\}$. If $q(t)\neq s\,w$ for every $t\in\mathbb{R}$ and every real $s\ge 0$ (so $q$ avoids the closed ray from $0$ through $w$, including $0$), then $q$ has winding number $0$.
--
--   A criterion for vanishing winding, for comparing windings of loops in $\mathbb{C}\setminus\{0\}$.
--
--   **Formalization Note** The conclusion is `HasLoopWind q 0` from `FiniteEnergyPlane_Winding`; the hypothesis is `∀ t, ∀ s : ℝ, 0 ≤ s → q t ≠ s * w` with `hw : w ≠ 0`.
-- source:
--   C. Wendl, Lectures on Symplectic Field Theory (2026 notes), arXiv:1612.01009, Section 3.7 (winding numbers of loops in C minus 0); standard.

import Definitions.Def_FiniteEnergyPlane_Winding

namespace FiniteEnergyPlane

/-- A continuous `1`-periodic loop in `ℂ` that misses a closed ray `{s w : s ≥ 0}` (`w ≠ 0`)
has winding number `0`. -/
theorem hasLoopWind_zero_of_forall_ne_ray (q : ℝ → ℂ) (hq : Continuous q)
    (hper : Function.Periodic q 1) (w : ℂ) (hw : w ≠ 0)
    (h : ∀ t, ∀ s : ℝ, 0 ≤ s → q t ≠ s * w) : HasLoopWind q 0 := by
  sorry

end FiniteEnergyPlane
