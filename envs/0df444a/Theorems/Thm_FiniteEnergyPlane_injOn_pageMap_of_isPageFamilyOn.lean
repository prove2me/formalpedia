-- Prove2me | Theorems.Thm_FiniteEnergyPlane_injOn_pageMap_of_isPageFamilyOn
-- name    : FiniteEnergyPlane.injOn_pageMap_of_isPageFamilyOn
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-11-22T18:05:19.318115+00:00
-- url     : https://prove2.me/theorems/b737c9b1-8007-48b5-85a2-456ad955b5e6
-- title:
--   Injectivity of the projection of a family of normalized fast planes near a time
-- statement:
--   Let $S=H^{-1}(1)\subset\mathbb{R}^4$ be a strictly star-shaped level, $J$ a smooth $d\lambda_0$-compatible complex structure on $\xi$, and $P=(x,T_P)$ a periodic Reeb orbit with $\mu_{CZ}(P)\ge3$ ($P$ may be degenerate). Let $y$ be a Reeb trajectory, $\gamma\in\mathbb{R}$, $l\ge1$, $I\subseteq\mathbb{R}$ open, and $U$ a family of class $C^l$ on $I\times\mathbb{C}$ with $U(t,\cdot)\in\Lambda(\{y(t)\},P)$ for every $t\in I$. Then for every $t_0\in I$ there is $\varepsilon>0$ with $(t_0-\varepsilon,t_0+\varepsilon)\subseteq I$ such that the map $(t,z)\mapsto\mathrm{pr}_S\,U(t,z)$ is injective on $(t_0-\varepsilon,t_0+\varepsilon)\times\mathbb{C}$.
--
--   This is Hryniewicz's Lemma 7.2. It is used for the local families of Lemma 7.3 and again for comparing families along a trajectory (Lemmas 7.4, 7.5 and Claim 7.6).
--
--   **Formalization Note** $\Lambda(\{y_0\},P)$ is `embeddedFastPlaneSet H J P {y₀} γ`, whose members satisfy $u(0)=y_0$ and have $d\lambda$-energy $\gamma$ on $\{|z|>1\}$. The family conditions are `IsPageFamilyOn H J P γ y l I U`, and $\mathrm{pr}_S\circ U$ is `pageMap H U`. $\mu_{CZ}(P)\ge3$ is `P.IsCZAtLeast 3`. Hryniewicz assumes only $C^1$; here $U$ is $C^l$ with $l\ge1$.
-- source:
--   U. Hryniewicz, Fast finite-energy planes in symplectizations and applications, Trans. Amer. Math. Soc. 364 (2012), 1859-1931, arXiv:0812.4076, Lemma 7.2

import Definitions.Def_FiniteEnergyPlane_OpenBook

namespace FiniteEnergyPlane

open MeasureTheory Metric Filter Topology
open scoped ContDiff ENNReal Real

/-- Hryniewicz (Trans. AMS 2012), Lemma 7.2. Let `P` be a periodic Reeb orbit of Conley–Zehnder
index at least `3`, `y` a Reeb trajectory, `I ⊆ ℝ` open and `U` a `C^l` family (`l ≥ 1`) on `I × ℂ`
with `U(t, ·) ∈ Λ({y t}, P)` for every `t ∈ I`. Then every `t₀ ∈ I` has a neighbourhood
`(t₀ - ε, t₀ + ε) ⊆ I` on whose product with `ℂ` the map `pageMap H U` is injective. -/
theorem injOn_pageMap_of_isPageFamilyOn (H : V 1 → ℝ) (hH : IsStrictlyStarShapedLevel H)
    (J : V 1 → V 1 →L[ℝ] V 1) (hJ : IsCompatibleXiStructure H J)
    (P : ReebOrbit H) (hcz : P.IsCZAtLeast 3) (γ : ℝ) (y : ℝ → V 1) (hy : IsReebTrajectory H y)
    (l : ℕ) (hl : 1 ≤ l) (I : Set ℝ) (hI : IsOpen I) (U : ℝ × ℂ → V 1)
    (hU : IsPageFamilyOn H J P γ y l I U) (t₀ : ℝ) (ht₀ : t₀ ∈ I) :
    ∃ ε > 0, ball t₀ ε ⊆ I ∧ Set.InjOn (pageMap H U) (ball t₀ ε ×ˢ Set.univ) := by
  sorry

end FiniteEnergyPlane
