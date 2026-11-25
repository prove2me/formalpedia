-- Prove2me | Theorems.Thm_FiniteEnergyPlane_injOn_pageMap_Ioo
-- name    : FiniteEnergyPlane.injOn_pageMap_Ioo
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-11-25T13:56:50.782035+00:00
-- url     : https://prove2.me/theorems/6aa5a281-32d2-5126-947e-9ba23964df81
-- title:
--   Families of pages are injective before the first return
-- statement:
--   Let $S=H^{-1}(1)\subset\mathbb{R}^4$ be a strictly star-shaped level, $J$ a smooth $d\lambda_0$-compatible complex structure on $\xi$, and $P=(x,T)$ a periodic Reeb orbit with $\mu_{CZ}(P)\ge3$. Suppose $0<\gamma<T$ and that $\Lambda(K,P)$ is sequentially compact in $C^\infty_{loc}$ for every compact $K\subset\mathbb{R}^4\setminus\{0\}$ disjoint from $\mathbb{R}\times x(\mathbb{R})$. Let $y$ be a Reeb trajectory, $l\ge1$, $I\subset\mathbb{R}$ open and $U=(a,u):I\times\mathbb{C}\to\mathbb{R}\times S$ a $C^l$ family with $U(t,\cdot)\in\Lambda(\{y(t)\},P)$ for $t\in I$. Suppose $[0,L]\subset I$, $y(L)\in u(0,\mathbb{C})$ and $y(t)\notin u(0,\mathbb{C})$ for $0<t<L$. Then $u$ is injective on $(0,L)\times\mathbb{C}$.
--
--   Reusable for constructing foliations by pages.
--
--   **Formalization Note** A family is `IsPageFamilyOn H J P γ y l I U`, its $S$-component is `pageMap H U`, and $\mathbb{R}\times S$ is $\mathbb{R}^4\setminus\{0\}$ with $y=e^{2a}x$.
-- source:
--   U. Hryniewicz, Fast finite-energy planes in symplectizations and applications, Trans. Amer. Math. Soc. 364 (2012), 1859-1931, arXiv:0812.4076, Section 7

import Definitions.Def_FiniteEnergyPlane_OpenBook

namespace FiniteEnergyPlane

open MeasureTheory Metric Filter Topology
open scoped ContDiff ENNReal Real

/-- Before the first return to the initial leaf a family of planes is injective in `S`. -/
theorem injOn_pageMap_Ioo (H : V 1 → ℝ)
    (hH : IsStrictlyStarShapedLevel H)
    (J : V 1 → V 1 →L[ℝ] V 1) (hJ : IsCompatibleXiStructure H J)
    (P : ReebOrbit H) (hcz : P.IsCZAtLeast 3) (γ : ℝ) (hγ : 0 < γ) (hγT : γ < P.T)
    (hΛ : ∀ K : Set (V 1), IsCompact K → (0 : V 1) ∉ K → (∀ y ∈ K, proj H y ∉ Set.range P.x) →
      IsSeqCompactCInftyLoc (embeddedFastPlaneSet H J P K γ))
    (y : ℝ → V 1) (hy : IsReebTrajectory H y)
    (l : ℕ) (hl : 1 ≤ l) (I : Set ℝ) (hI : IsOpen I) (U : ℝ × ℂ → V 1)
    (hU : IsPageFamilyOn H J P γ y l I U) (L : ℝ) (hLI : Set.Icc 0 L ⊆ I)
    (hyL : y L ∈ Set.range (fun z => pageMap H U (0, z)))
    (hmin : ∀ t ∈ Set.Ioo 0 L, y t ∉ Set.range (fun z => pageMap H U (0, z))) :
    Set.InjOn (pageMap H U) (Set.Ioo 0 L ×ˢ Set.univ) := by
  sorry

end FiniteEnergyPlane
