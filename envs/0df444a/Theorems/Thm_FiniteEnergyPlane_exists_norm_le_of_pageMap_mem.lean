-- Prove2me | Theorems.Thm_FiniteEnergyPlane_exists_norm_le_of_pageMap_mem
-- name    : FiniteEnergyPlane.exists_norm_le_of_pageMap_mem
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-11-25T13:46:22.942047+00:00
-- url     : https://prove2.me/theorems/e7c6e6d7-7d3b-5e0b-a1e2-2a4c1e9a9d0e
-- title:
--   Uniform properness of families of pages
-- statement:
--   Let $S=H^{-1}(1)\subset\mathbb{R}^4$ be a strictly star-shaped level, $J$ a smooth $d\lambda_0$-compatible complex structure on $\xi$, and $P=(x,T)$ a periodic Reeb orbit with $\mu_{CZ}(P)\ge3$. Suppose $0<\gamma<T$ and that $\Lambda(K,P)$ is sequentially compact in $C^\infty_{loc}$ for every compact $K\subset\mathbb{R}^4\setminus\{0\}$ disjoint from $\mathbb{R}\times x(\mathbb{R})$. Let $y$ be a Reeb trajectory, $l\ge1$, $I\subset\mathbb{R}$ open and $U=(a,u):I\times\mathbb{C}\to\mathbb{R}\times S$ a $C^l$ family with $U(t,\cdot)\in\Lambda(\{y(t)\},P)$ for $t\in I$. If $[a,b]\subset I$ and $K$ is compact and disjoint from $x(\mathbb{R})$, then there is $r$ with $|z|\le r$ whenever $t\in[a,b]$ and $u(t,z)\in K$.
--
--   Reusable for closedness of unions of leaves away from the binding.
--
--   **Formalization Note** A family is `IsPageFamilyOn H J P γ y l I U`, its $S$-component is `pageMap H U`, and $\mathbb{R}\times S$ is $\mathbb{R}^4\setminus\{0\}$ with $y=e^{2a}x$.
-- source:
--   U. Hryniewicz, Fast finite-energy planes in symplectizations and applications, Trans. Amer. Math. Soc. 364 (2012), 1859-1931, arXiv:0812.4076, Section 7

import Definitions.Def_FiniteEnergyPlane_OpenBook

namespace FiniteEnergyPlane

open MeasureTheory Metric Filter Topology
open scoped ContDiff ENNReal Real

/-- A compact subset of the complement of `x(ℝ)` meets the leaves of a family only at bounded parameters, uniformly on compact time intervals. -/
theorem exists_norm_le_of_pageMap_mem (H : V 1 → ℝ)
    (hH : IsStrictlyStarShapedLevel H)
    (J : V 1 → V 1 →L[ℝ] V 1) (hJ : IsCompatibleXiStructure H J)
    (P : ReebOrbit H) (hcz : P.IsCZAtLeast 3) (γ : ℝ) (hγ : 0 < γ) (hγT : γ < P.T)
    (hΛ : ∀ K : Set (V 1), IsCompact K → (0 : V 1) ∉ K → (∀ y ∈ K, proj H y ∉ Set.range P.x) →
      IsSeqCompactCInftyLoc (embeddedFastPlaneSet H J P K γ))
    (y : ℝ → V 1) (hy : IsReebTrajectory H y)
    (l : ℕ) (hl : 1 ≤ l) (I : Set ℝ) (hI : IsOpen I) (U : ℝ × ℂ → V 1)
    (hU : IsPageFamilyOn H J P γ y l I U) (a b : ℝ) (hab : Set.Icc a b ⊆ I)
    (K : Set (V 1)) (hK : IsCompact K) (hKP : Disjoint K (Set.range P.x)) :
    ∃ r : ℝ, ∀ t ∈ Set.Icc a b, ∀ z, pageMap H U (t, z) ∈ K → ‖z‖ ≤ r := by
  sorry

end FiniteEnergyPlane
