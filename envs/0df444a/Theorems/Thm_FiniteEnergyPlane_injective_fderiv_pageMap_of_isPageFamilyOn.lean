-- Prove2me | Theorems.Thm_FiniteEnergyPlane_injective_fderiv_pageMap_of_isPageFamilyOn
-- name    : FiniteEnergyPlane.injective_fderiv_pageMap_of_isPageFamilyOn
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-11-25T12:57:14.130799+00:00
-- url     : https://prove2.me/theorems/db6d3059-ad41-5296-9bfe-41c4ae2e6f09
-- title:
--   Families of pages are immersed
-- statement:
--   Let $S=H^{-1}(1)\subset\mathbb{R}^4$ be a strictly star-shaped level, $J$ a smooth $d\lambda_0$-compatible complex structure on $\xi$, and $P=(x,T)$ a periodic Reeb orbit with $\mu_{CZ}(P)\ge3$. Let $y$ be a Reeb trajectory, $l\ge1$, $I\subset\mathbb{R}$ open and $U=(a,u):I\times\mathbb{C}\to\mathbb{R}\times S$ a $C^l$ family with $U(t,\cdot)\in\Lambda(\{y(t)\},P)$ for $t\in I$. Then the derivative of $u$ is injective at every point of $I\times\mathbb{C}$.
--
--   Reusable for openness and transversality of families of pages.
--
--   **Formalization Note** A family is `IsPageFamilyOn H J P γ y l I U`, its $S$-component is `pageMap H U`, and $\mathbb{R}\times S$ is $\mathbb{R}^4\setminus\{0\}$ with $y=e^{2a}x$.
-- source:
--   U. Hryniewicz, Fast finite-energy planes in symplectizations and applications, Trans. Amer. Math. Soc. 364 (2012), 1859-1931, arXiv:0812.4076, Section 7

import Definitions.Def_FiniteEnergyPlane_OpenBook

namespace FiniteEnergyPlane

open MeasureTheory Metric Filter Topology
open scoped ContDiff ENNReal Real

/-- Every `C^l` family of planes along a Reeb trajectory is immersed in `S`. -/
theorem injective_fderiv_pageMap_of_isPageFamilyOn (H : V 1 → ℝ)
    (hH : IsStrictlyStarShapedLevel H)
    (J : V 1 → V 1 →L[ℝ] V 1) (hJ : IsCompatibleXiStructure H J)
    (P : ReebOrbit H) (hcz : P.IsCZAtLeast 3) (γ : ℝ) (y : ℝ → V 1) (hy : IsReebTrajectory H y)
    (l : ℕ) (hl : 1 ≤ l) (I : Set ℝ) (hI : IsOpen I) (U : ℝ × ℂ → V 1)
    (hU : IsPageFamilyOn H J P γ y l I U) (t : ℝ) (ht : t ∈ I) (z : ℂ) :
    Function.Injective (fderiv ℝ (pageMap H U) (t, z)) := by
  sorry

end FiniteEnergyPlane
