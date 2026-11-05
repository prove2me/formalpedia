-- Prove2me | Theorems.Thm_FiniteEnergyPlane_exists_page_family_along_trajectory
-- name    : FiniteEnergyPlane.exists_page_family_along_trajectory
-- status  : Open
-- author  : @Mazecto
-- created : 2026-11-04T15:48:21.935889+00:00
-- url     : https://prove2.me/theorems/02dd2127-aa2b-4d24-9f98-18573d4a2c8c
-- title:
--   Families of normalized fast planes along any finite piece of a Reeb trajectory
-- statement:
--   Let $S=H^{-1}(1)\subset\mathbb{R}^4$ be a strictly star-shaped level, $J$ a smooth $d\lambda_0$-compatible complex structure on $\xi$, and $P=(x,T_P)$ a periodic Reeb orbit with $\mu_{CZ}(P)\ge3$ ($P$ may be degenerate unless stated otherwise). Let $\gamma\in\mathbb{R}$ be such that $\Lambda(K,P)$ is sequentially compact in $C^\infty_{loc}(\mathbb{C},\mathbb{R}^4)$ for every compact $K\subset\mathbb{R}^4\setminus\{0\}$ with $K\cap(\mathbb{R}\times x(\mathbb{R}))=\emptyset$. Let $y$ be a Reeb trajectory, $v\in\Lambda(\{y(0)\},P)$, $l\ge1$ and $\tau>0$. Then there are $\delta>0$ and a $C^l$ family $U$ with `IsPageFamilyOn` on $(-\delta,\tau)\times\mathbb{C}$ along $y$, and $U(0,\cdot)=v$.
--
--   **Formalization Note** The hypothesis on $\Lambda(K,P)$ is exactly the conclusion of `isSeqCompact_embeddedFastPlaneSet` for the same $\gamma$, quantified over $K$; the cylinder $\mathbb{R}\times x(\mathbb{R})$ is the cone $\{y\neq0:\mathrm{proj}(y)\in x(\mathbb{R})\}$. $\mu_{CZ}(P)\ge3$ is `P.IsCZAtLeast 3`, the index of the linearized flow along $P$ in the global frame of $\xi$. Hryniewicz writes $\mu(\tilde u)=k\ge3$ and restricts to $\Lambda_k$; on a strictly star-shaped level $\xi$ has a global frame, which extends over every capping disk, so the index depends only on $P$, $\Lambda_k=\Lambda$, and the condition is not restated.
-- source:
--   U. Hryniewicz, Fast finite-energy planes in symplectizations and applications, Trans. Amer. Math. Soc. 364 (2012), 1859–1931, arXiv:0812.4076, Lemma 7.8

import Definitions.Def_FiniteEnergyPlane_OpenBook

namespace FiniteEnergyPlane

open MeasureTheory Metric Filter Topology
open scoped ContDiff ENNReal Real

/-- Hryniewicz (Trans. AMS 2012), Lemma 7.8. Let `P` be a periodic Reeb orbit of Conley–Zehnder index
at least `3` such that `Λ(K, P)` is sequentially compact in `C^∞_loc` for every compact
`K ⊂ V 1 \ {0}` disjoint from the cone `ℝ × x(ℝ)`. If `y` is a Reeb trajectory and
`v ∈ Λ({y 0}, P)`, then for all `l ≥ 1` and `τ > 0` there are `δ > 0` and a `C^l` family `U` along
`y` on `(-δ, τ) × ℂ` with `U(0, ·) = v`. -/
theorem exists_page_family_along_trajectory (H : V 1 → ℝ) (hH : IsStrictlyStarShapedLevel H)
    (J : V 1 → V 1 →L[ℝ] V 1) (hJ : IsCompatibleXiStructure H J)
    (P : ReebOrbit H) (hcz : P.IsCZAtLeast 3) (γ : ℝ)
    (hΛ : ∀ K : Set (V 1), IsCompact K → (0 : V 1) ∉ K → (∀ y ∈ K, proj H y ∉ Set.range P.x) →
      IsSeqCompactCInftyLoc (embeddedFastPlaneSet H J P K γ))
    (y : ℝ → V 1) (hy : IsReebTrajectory H y) (v : ℂ → V 1)
    (hv : v ∈ embeddedFastPlaneSet H J P {y 0} γ) (l : ℕ) (hl : 1 ≤ l) (τ : ℝ) (hτ : 0 < τ) :
    ∃ δ > 0, ∃ U : ℝ × ℂ → V 1, IsPageFamilyOn H J P γ y l (Set.Ioo (-δ) τ) U ∧
      ∀ z, U (0, z) = v z := by
  sorry

end FiniteEnergyPlane
