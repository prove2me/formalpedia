-- Prove2me | Theorems.Thm_FiniteEnergyPlane_exists_pageFamily_injective_fderiv
-- name    : FiniteEnergyPlane.exists_pageFamily_injective_fderiv
-- status  : Open
-- author  : @Mazecto
-- created : 2026-11-22T18:05:15.795636+00:00
-- url     : https://prove2.me/theorems/bb7e0460-b303-4d4b-8f55-fce98e5d8501
-- title:
--   Local C^l families of normalized fast planes with immersed projection
-- statement:
--   Let $S=H^{-1}(1)\subset\mathbb{R}^4$ be a strictly star-shaped level, $J$ a smooth $d\lambda_0$-compatible complex structure on $\xi$, and $P=(x,T_P)$ a periodic Reeb orbit with $\mu_{CZ}(P)\ge3$ ($P$ may be degenerate). Let $y$ be a Reeb trajectory, $t_0,\gamma\in\mathbb{R}$, $u_0\in\Lambda(\{y(t_0)\},P)$ and $l\ge1$. Then there are $\varepsilon>0$ and a family $U$, of class $C^l$ on $I\times\mathbb{C}$ with $I=(t_0-\varepsilon,t_0+\varepsilon)$, such that $U(t_0,\cdot)=u_0$, $U(t,\cdot)\in\Lambda(\{y(t)\},P)$ for every $t\in I$, and the map $(t,z)\mapsto\mathrm{pr}_S\,U(t,z)$ into $S$ has injective derivative at every point of $I\times\mathbb{C}$.
--
--   This is the existence part of Hryniewicz's Lemma 7.3: together with the injectivity of Lemma 7.2 it makes $\mathrm{pr}_S\circ U$ an embedding of $I\times\mathbb{C}$ into $S$.
--
--   **Formalization Note** $\Lambda(\{y_0\},P)$ is `embeddedFastPlaneSet H J P {y₀} γ`, whose members satisfy $u(0)=y_0$ and have $d\lambda$-energy $\gamma$ on $\{|z|>1\}$. The family conditions ($C^l$ on $I\times\mathbb{C}$, slices in $\Lambda(\{y(t)\},P)$) are `IsPageFamilyOn H J P γ y l I U`, and $\mathrm{pr}_S\circ U$ is `pageMap H U`. $\mu_{CZ}(P)\ge3$ is `P.IsCZAtLeast 3`.
-- source:
--   U. Hryniewicz, Fast finite-energy planes in symplectizations and applications, Trans. Amer. Math. Soc. 364 (2012), 1859-1931, arXiv:0812.4076, Lemma 7.3

import Definitions.Def_FiniteEnergyPlane_OpenBook

namespace FiniteEnergyPlane

open MeasureTheory Metric Filter Topology
open scoped ContDiff ENNReal Real

/-- Hryniewicz (Trans. AMS 2012), Lemma 7.3 (existence part). Let `P` be a periodic Reeb orbit of
Conley–Zehnder index at least `3`, `y` a Reeb trajectory and `u₀ ∈ Λ({y t₀}, P)`. For every `l ≥ 1`
there are `ε > 0` and a `C^l` family `U` on `(t₀ - ε, t₀ + ε) × ℂ` with `U(t₀, ·) = u₀` and
`U(t, ·) ∈ Λ({y t}, P)` whose map `pageMap H U` has injective derivative at every point of
`(t₀ - ε, t₀ + ε) × ℂ`. -/
theorem exists_pageFamily_injective_fderiv (H : V 1 → ℝ) (hH : IsStrictlyStarShapedLevel H)
    (J : V 1 → V 1 →L[ℝ] V 1) (hJ : IsCompatibleXiStructure H J)
    (P : ReebOrbit H) (hcz : P.IsCZAtLeast 3) (γ : ℝ) (y : ℝ → V 1) (hy : IsReebTrajectory H y)
    (t₀ : ℝ) (u₀ : ℂ → V 1) (hu₀ : u₀ ∈ embeddedFastPlaneSet H J P {y t₀} γ)
    (l : ℕ) (hl : 1 ≤ l) :
    ∃ ε > 0, ∃ U : ℝ × ℂ → V 1, IsPageFamilyOn H J P γ y l (ball t₀ ε) U ∧
      (∀ z, U (t₀, z) = u₀ z) ∧
      ∀ p ∈ ball t₀ ε ×ˢ (Set.univ : Set ℂ), Function.Injective (fderiv ℝ (pageMap H U) p) := by
  sorry

end FiniteEnergyPlane
