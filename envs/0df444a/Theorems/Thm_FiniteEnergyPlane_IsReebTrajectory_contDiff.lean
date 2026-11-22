-- Prove2me | Theorems.Thm_FiniteEnergyPlane_IsReebTrajectory_contDiff
-- name    : FiniteEnergyPlane.IsReebTrajectory.contDiff
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-11-22T19:27:13.280804+00:00
-- url     : https://prove2.me/theorems/867d2ee4-ce70-46eb-b788-7a996dffb684
-- title:
--   Reeb trajectories on a strictly star-shaped level are smooth
-- statement:
--   Let $S=H^{-1}(1)\subset\mathbb{R}^{2n+2}$ be a strictly star-shaped level of a smooth $H$ and let $y:\mathbb{R}\to\mathbb{R}^{2n+2}$ be a trajectory of the Reeb vector field $R$ of $\lambda_0|_S$: $y(t)\in S$ and $y'(t)=R(y(t))$ for every $t$. Then $y$ is of class $C^\infty$.
--
--   It provides the regularity in time needed to follow a Reeb trajectory with families of planes of class $C^l$.
--
--   **Formalization Note** $\mathbb{R}^{2n+2}$ is `V n`, the strictly star-shaped condition is `IsStrictlyStarShapedLevel H`, and "trajectory of $R$" is `IsReebTrajectory H y`.
-- source:
--   U. Hryniewicz, Fast finite-energy planes in symplectizations and applications, Trans. Amer. Math. Soc. 364 (2012), 1859-1931, arXiv:0812.4076, Section 7.1

import Definitions.Def_FiniteEnergyPlane_OpenBook

namespace FiniteEnergyPlane

open MeasureTheory Metric Filter Topology
open scoped ContDiff ENNReal Real

/-- On a strictly star-shaped level `S = H⁻¹(1)`, every Reeb trajectory `y : ℝ → V n` is `C^∞`. -/
theorem IsReebTrajectory.contDiff {n : ℕ} {H : V n → ℝ} (hH : IsStrictlyStarShapedLevel H)
    {y : ℝ → V n} (hy : IsReebTrajectory H y) : ContDiff ℝ ∞ y := by
  sorry

end FiniteEnergyPlane
