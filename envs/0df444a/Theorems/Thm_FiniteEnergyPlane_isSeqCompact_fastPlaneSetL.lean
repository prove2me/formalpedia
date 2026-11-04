-- Prove2me | Theorems.Thm_FiniteEnergyPlane_isSeqCompact_fastPlaneSetL
-- name    : FiniteEnergyPlane.isSeqCompact_fastPlaneSetL
-- status  : Open
-- author  : @Mazecto
-- created : 2026-11-03T16:26:06.85142+00:00
-- url     : https://prove2.me/theorems/1dd1ac4d-42c7-4e83-b5e3-234e173e21c7
-- title:
--   Compactness of fast planes with a lower bound on the $\mathbb{R}$-coordinate
-- statement:
--   Let $S=H^{-1}(1)\subset\mathbb{R}^4$ be a strictly star-shaped level and $J$ a smooth $d\lambda_0$-compatible complex structure on $\xi$. Let $P$ be a periodic Reeb orbit such that every periodic Reeb orbit of period at most $T_P$ is nondegenerate with $\mu_{CZ}\ge3$, let $\gamma>0$ be smaller than every such period and than every difference of two distinct such periods, and let $K\subset\mathbb{R}^4\setminus\{0\}$ be compact. Then for every $L\in\mathbb{R}$ the set $\Theta_L(K,P)$ is sequentially compact in $C^\infty_{loc}(\mathbb{C},\mathbb{R}^4)$.
--
--   **Formalization Note** Periods are those of `ReebOrbit H` (not necessarily minimal, so multiple covers count); $\mu_{CZ}\ge3$ is `Q.IsCZAtLeast 3`. $\Theta_L(K,P)$ is `fastPlaneSetL H J P K γ L`.
-- source:
--   U. Hryniewicz, Fast finite-energy planes in symplectizations and applications, Trans. Amer. Math. Soc. 364 (2012), 1859–1931, arXiv:0812.4076, Theorem 2.2 (1)

import Definitions.Def_FiniteEnergyPlane_Compactness

namespace FiniteEnergyPlane

open MeasureTheory Metric Filter Topology
open scoped ContDiff ENNReal Real

/-- Hryniewicz (Trans. AMS 2012), Theorem 2.2 (1), for `Θ_L`. Let `P` be a periodic Reeb orbit on
`S ⊂ ℝ⁴` such that every periodic orbit of period at most `P.T` is nondegenerate with
Conley–Zehnder index at least `3`, let `0 < γ` be smaller than every such period and every
difference of two distinct such periods, and let `K ⊂ V 1 \ {0}` be compact. Then for every `L`
the set `Θ_L(K, P)` of planes in `fastPlaneSet H J P K γ` with `aCoord H ∘ u ≥ -L` is sequentially
compact in `C^∞_loc(ℂ, V 1)`. -/
theorem isSeqCompact_fastPlaneSetL (H : V 1 → ℝ) (hH : IsStrictlyStarShapedLevel H)
    (J : V 1 → V 1 →L[ℝ] V 1) (hJ : IsCompatibleXiStructure H J)
    (P : ReebOrbit H)
    (hP : ∀ Q : ReebOrbit H, Q.T ≤ P.T → Q.IsNondegenerate ∧ Q.IsCZAtLeast 3)
    (γ : ℝ) (hγ : 0 < γ) (hγ₁ : ∀ Q : ReebOrbit H, Q.T ≤ P.T → γ < Q.T)
    (hγ₂ : ∀ Q₁ Q₂ : ReebOrbit H, Q₁.T ≤ P.T → Q₂.T ≤ P.T → Q₁.T ≠ Q₂.T → γ < |Q₁.T - Q₂.T|)
    (K : Set (V 1)) (hK : IsCompact K) (hK0 : (0 : V 1) ∉ K) (L : ℝ) :
    IsSeqCompactCInftyLoc (fastPlaneSetL H J P K γ L) := by
  sorry

end FiniteEnergyPlane
