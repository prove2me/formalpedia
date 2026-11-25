-- Prove2me | Theorems.Thm_FiniteEnergyPlane_isReebPositiveAt_of_isPageFamilyOn
-- name    : FiniteEnergyPlane.isReebPositiveAt_of_isPageFamilyOn
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-11-25T13:24:04.445657+00:00
-- url     : https://prove2.me/theorems/03902449-b3b1-5e61-a1b0-66cc2032f2af
-- title:
--   Families of pages are positive against the Reeb field
-- statement:
--   Let $S=H^{-1}(1)\subset\mathbb{R}^4$ be a strictly star-shaped level, $J$ a smooth $d\lambda_0$-compatible complex structure on $\xi$, and $P=(x,T)$ a periodic Reeb orbit with $\mu_{CZ}(P)\ge3$. Let $y$ be a Reeb trajectory, $l\ge1$, $I\subset\mathbb{R}$ open and $U=(a,u):I\times\mathbb{C}\to\mathbb{R}\times S$ a $C^l$ family with $U(t,\cdot)\in\Lambda(\{y(t)\},P)$ for $t\in I$. Then at every point of $I\times\mathbb{C}$ the Reeb vector is the image under the derivative of $u$ of a vector with positive $\mathbb{R}$-component.
--
--   Reusable for orientation statements about families of pages.
--
--   **Formalization Note** A family is `IsPageFamilyOn H J P γ y l I U`, its $S$-component is `pageMap H U`, and $\mathbb{R}\times S$ is $\mathbb{R}^4\setminus\{0\}$ with $y=e^{2a}x$.
-- source:
--   U. Hryniewicz, Fast finite-energy planes in symplectizations and applications, Trans. Amer. Math. Soc. 364 (2012), 1859-1931, arXiv:0812.4076, Section 7

import Definitions.Def_FiniteEnergyPlane_OpenBook

namespace FiniteEnergyPlane

open MeasureTheory Metric Filter Topology
open scoped ContDiff ENNReal Real

/-- Every `C^l` family of planes along a Reeb trajectory is positive against the Reeb field. -/
theorem isReebPositiveAt_of_isPageFamilyOn (H : V 1 → ℝ)
    (hH : IsStrictlyStarShapedLevel H)
    (J : V 1 → V 1 →L[ℝ] V 1) (hJ : IsCompatibleXiStructure H J)
    (P : ReebOrbit H) (hcz : P.IsCZAtLeast 3) (γ : ℝ) (y : ℝ → V 1) (hy : IsReebTrajectory H y)
    (l : ℕ) (hl : 1 ≤ l) (I : Set ℝ) (hI : IsOpen I) (U : ℝ × ℂ → V 1)
    (hU : IsPageFamilyOn H J P γ y l I U) (t : ℝ) (ht : t ∈ I) (z : ℂ) :
    IsReebPositiveAt H U (t, z) := by
  sorry

end FiniteEnergyPlane
