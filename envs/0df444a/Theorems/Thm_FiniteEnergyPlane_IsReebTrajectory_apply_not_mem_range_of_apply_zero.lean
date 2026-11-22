-- Prove2me | Theorems.Thm_FiniteEnergyPlane_IsReebTrajectory_apply_not_mem_range_of_apply_zero
-- name    : FiniteEnergyPlane.IsReebTrajectory.apply_not_mem_range_of_apply_zero
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-11-21T12:29:08.789287+00:00
-- url     : https://prove2.me/theorems/5311cacd-5856-4ae7-87da-c35a53099d28
-- title:
--   A Reeb trajectory starting off a periodic orbit never meets it
-- statement:
--   Let $S = H^{-1}(1)$ be a strictly star-shaped level in $\mathbb{R}^{2n+2}$ with Reeb vector field $R$, and let $P = (x, T)$ be a periodic Reeb orbit on $S$. If $y : \mathbb{R} \to S$ is a Reeb trajectory, $\dot y = R(y)$, whose initial point $y(0)$ does not lie on $x(\mathbb{R})$, then $y(t) \notin x(\mathbb{R})$ for every $t \in \mathbb{R}$.
--
--   Role: a basic invariance property of the Reeb flow. It lets results about trajectories off a periodic orbit be applied to every time-shift of such a trajectory.
--
--   Formalization Note: `IsReebTrajectory H y` means $y(t) \in S$ and $y'(t) = R(y(t))$ for all $t$. The orbit's image is `Set.range P.x`.
-- source:
--   Standard ODE uniqueness for the Reeb flow on a strictly star-shaped level; used in U. Hryniewicz, Fast finite-energy planes in symplectizations and applications, Trans. AMS 364 (2012), Section 6.2

import Definitions.Def_FiniteEnergyPlane_OpenBook

namespace FiniteEnergyPlane

open MeasureTheory Metric Filter Topology
open scoped ContDiff ENNReal Real

/-- On a strictly star-shaped level `S = H⁻¹(1)`, a Reeb trajectory `y` whose initial point
`y 0` does not lie on the periodic Reeb orbit `P` never meets `x(ℝ)`. -/
theorem IsReebTrajectory.apply_not_mem_range_of_apply_zero {n : ℕ} {H : V n → ℝ}
    (hH : IsStrictlyStarShapedLevel H) (P : ReebOrbit H) {y : ℝ → V n}
    (hy : IsReebTrajectory H y) (hy₀ : y 0 ∉ Set.range P.x) :
    ∀ t, y t ∉ Set.range P.x := by
  sorry

end FiniteEnergyPlane
