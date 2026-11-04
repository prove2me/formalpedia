-- Prove2me | Theorems.Thm_FiniteEnergyPlane_isSeqCompact_embeddedFastPlaneSet
-- name    : FiniteEnergyPlane.isSeqCompact_embeddedFastPlaneSet
-- status  : Open
-- author  : @Mazecto
-- created : 2026-11-03T21:11:26.731061+00:00
-- url     : https://prove2.me/theorems/45cf50fd-ef69-4a86-8652-f6c7f76c8daa
-- title:
--   Compactness of embedded fast finite-energy planes
-- statement:
--   Let $S=H^{-1}(1)\subset\mathbb{R}^4$ be a strictly star-shaped level and $J$ a smooth $d\lambda_0$-compatible complex structure on $\xi$. Let $P$ be a periodic Reeb orbit such that every periodic Reeb orbit of period at most $T_P$ is nondegenerate with $\mu_{CZ}\ge3$, let $\gamma>0$ be smaller than every such period and than every difference of two distinct such periods, and let $K\subset\mathbb{R}^4\setminus\{0\}$ be compact with $K\cap(\mathbb{R}\times x(\mathbb{R}))=\emptyset$, where $P=(x,T_P)$. Then $\Lambda(K,P)$ is sequentially compact in $C^\infty_{loc}(\mathbb{C},\mathbb{R}^4)$.
--
--   **Formalization Note** Periods are those of `ReebOrbit H` (not necessarily minimal, so multiple covers count); $\mu_{CZ}\ge3$ is `Q.IsCZAtLeast 3`. The cylinder $\mathbb{R}\times x(\mathbb{R})$ is the cone $\{y\neq0:\mathrm{proj}(y)\in x(\mathbb{R})\}$. $\Lambda(K,P)$ is `embeddedFastPlaneSet H J P K γ`; sequential compactness is `IsSeqCompactCInftyLoc`.
-- source:
--   U. Hryniewicz, Fast finite-energy planes in symplectizations and applications, Trans. Amer. Math. Soc. 364 (2012), 1859–1931, arXiv:0812.4076, Theorem 2.2 (2)

import Definitions.Def_FiniteEnergyPlane_Fredholm

namespace FiniteEnergyPlane

open MeasureTheory Metric Filter Topology
open scoped ContDiff ENNReal Real

/-- Hryniewicz (Trans. AMS 2012), Theorem 2.2 (2), for `Λ`. Let `P` be a periodic Reeb orbit such
that every periodic orbit of period at most `P.T` is nondegenerate with Conley–Zehnder index at
least `3`, let `0 < γ` be smaller than every period at most `P.T` and every difference of two
distinct such periods, and let `K ⊂ V 1 \ {0}` be a compact set disjoint from the cone
`ℝ × x(ℝ)`. Then the set `Λ(K, P)` of embedded planes in `Θ(K, P)` is sequentially compact in
`C^∞_loc(ℂ, V 1)`. -/
theorem isSeqCompact_embeddedFastPlaneSet (H : V 1 → ℝ) (hH : IsStrictlyStarShapedLevel H)
    (J : V 1 → V 1 →L[ℝ] V 1) (hJ : IsCompatibleXiStructure H J)
    (P : ReebOrbit H)
    (hP : ∀ Q : ReebOrbit H, Q.T ≤ P.T → Q.IsNondegenerate ∧ Q.IsCZAtLeast 3)
    (γ : ℝ) (hγ : 0 < γ) (hγ₁ : ∀ Q : ReebOrbit H, Q.T ≤ P.T → γ < Q.T)
    (hγ₂ : ∀ Q₁ Q₂ : ReebOrbit H, Q₁.T ≤ P.T → Q₂.T ≤ P.T → Q₁.T ≠ Q₂.T → γ < |Q₁.T - Q₂.T|)
    (K : Set (V 1)) (hK : IsCompact K) (hK₀ : (0 : V 1) ∉ K)
    (hKP : ∀ y ∈ K, proj H y ∉ Set.range P.x) :
    IsSeqCompactCInftyLoc (embeddedFastPlaneSet H J P K γ) := by
  sorry

end FiniteEnergyPlane
