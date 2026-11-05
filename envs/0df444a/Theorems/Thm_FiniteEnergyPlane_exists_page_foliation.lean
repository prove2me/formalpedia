-- Prove2me | Theorems.Thm_FiniteEnergyPlane_exists_page_foliation
-- name    : FiniteEnergyPlane.exists_page_foliation
-- status  : Open
-- author  : @Mazecto
-- created : 2026-11-04T15:49:18.280196+00:00
-- url     : https://prove2.me/theorems/8846a2c3-e247-4d42-b55d-f894644d4055
-- title:
--   Foliating the complement of a leaf and of $P$
-- statement:
--   Let $S=H^{-1}(1)\subset\mathbb{R}^4$ be a strictly star-shaped level, $J$ a smooth $d\lambda_0$-compatible complex structure on $\xi$, and $P=(x,T_P)$ a periodic Reeb orbit with $\mu_{CZ}(P)\ge3$ ($P$ may be degenerate unless stated otherwise). Suppose every periodic Reeb orbit of period at most $T_P$ is nondegenerate, $\gamma>0$ is smaller than every such period and than every difference of two distinct such periods, and $\Lambda(K,P)$ is sequentially compact in $C^\infty_{loc}(\mathbb{C},\mathbb{R}^4)$ for every compact $K\subset\mathbb{R}^4\setminus\{0\}$ with $K\cap(\mathbb{R}\times x(\mathbb{R}))=\emptyset$. Let $y$ be a Reeb trajectory, $v\in\Lambda(\{y(0)\},P)$ and $\tau>0$ with $y(\tau)\in\mathrm{proj}(v(\mathbb{C}))$. Then for every $l\ge1$ there are $L,\delta>0$ and a family $U$ with `IsPageFoliation H J P γ y l L δ U` and $U(0,\cdot)=v$.
--
--   **Formalization Note** Periods are those of `ReebOrbit H` (not necessarily minimal, so multiple covers count). The hypothesis on $\Lambda(K,P)$ is exactly the conclusion of `isSeqCompact_embeddedFastPlaneSet` for the same $\gamma$, quantified over $K$; the cylinder $\mathbb{R}\times x(\mathbb{R})$ is the cone $\{y\neq0:\mathrm{proj}(y)\in x(\mathbb{R})\}$. $\mu_{CZ}(P)\ge3$ is `P.IsCZAtLeast 3`, the index of the linearized flow along $P$ in the global frame of $\xi$. Hryniewicz writes $\mu(\tilde u)=k\ge3$ and restricts to $\Lambda_k$; on a strictly star-shaped level $\xi$ has a global frame, which extends over every capping disk, so the index depends only on $P$, $\Lambda_k=\Lambda$, and the condition is not restated. Hryniewicz assumes every contractible orbit nondegenerate; only orbits of period at most $T_P$ appear here. On a star-shaped level every orbit is contractible.
-- source:
--   U. Hryniewicz, Fast finite-energy planes in symplectizations and applications, Trans. Amer. Math. Soc. 364 (2012), 1859–1931, arXiv:0812.4076, Lemma 7.7

import Definitions.Def_FiniteEnergyPlane_OpenBook

namespace FiniteEnergyPlane

open MeasureTheory Metric Filter Topology
open scoped ContDiff ENNReal Real

/-- Hryniewicz (Trans. AMS 2012), Lemma 7.7. Let `P` be a periodic Reeb orbit of Conley–Zehnder index
at least `3` such that every periodic orbit of period at most `P.T` is nondegenerate; let `0 < γ` be
smaller than every such period and every difference of two distinct such periods, and suppose
`Λ(K, P)` is sequentially compact in `C^∞_loc` for every compact `K ⊂ V 1 \ {0}` disjoint from the
cone `ℝ × x(ℝ)`. Let `y` be a Reeb trajectory and `v ∈ Λ({y 0}, P)` such that `y τ` lies in the image
of `proj H ∘ v` for some `τ > 0`. Then for every `l ≥ 1` there are `L, δ > 0` and a `C^l` family `U`
with `U(0, ·) = v` satisfying `IsPageFoliation`: its leaves at `t = 0` and `t = L` have the same
image, and `(0, L) × ℂ` parametrizes the complement in `S` of this leaf and of `x(ℝ)`. -/
theorem exists_page_foliation (H : V 1 → ℝ) (hH : IsStrictlyStarShapedLevel H)
    (J : V 1 → V 1 →L[ℝ] V 1) (hJ : IsCompatibleXiStructure H J)
    (P : ReebOrbit H) (hcz : P.IsCZAtLeast 3) (hnd : ∀ Q : ReebOrbit H, Q.T ≤ P.T → Q.IsNondegenerate)
    (γ : ℝ) (hγ : 0 < γ) (hγ₁ : ∀ Q : ReebOrbit H, Q.T ≤ P.T → γ < Q.T)
    (hγ₂ : ∀ Q₁ Q₂ : ReebOrbit H, Q₁.T ≤ P.T → Q₂.T ≤ P.T → Q₁.T ≠ Q₂.T → γ < |Q₁.T - Q₂.T|)
    (hΛ : ∀ K : Set (V 1), IsCompact K → (0 : V 1) ∉ K → (∀ y ∈ K, proj H y ∉ Set.range P.x) →
      IsSeqCompactCInftyLoc (embeddedFastPlaneSet H J P K γ))
    (y : ℝ → V 1) (hy : IsReebTrajectory H y) (v : ℂ → V 1)
    (hv : v ∈ embeddedFastPlaneSet H J P {y 0} γ) (τ : ℝ) (hτ : 0 < τ)
    (hret : y τ ∈ Set.range (fun z => proj H (v z))) (l : ℕ) (hl : 1 ≤ l) :
    ∃ L > 0, ∃ δ > 0, ∃ U : ℝ × ℂ → V 1, IsPageFoliation H J P γ y l L δ U ∧
      ∀ z, U (0, z) = v z := by
  sorry

end FiniteEnergyPlane
