-- Prove2me | Theorems.Thm_FiniteEnergyPlane_embeddedFastPlaneSet_nonempty_of_isReebTrajectory
-- name    : FiniteEnergyPlane.embeddedFastPlaneSet_nonempty_of_isReebTrajectory
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-11-23T22:40:03.747456+00:00
-- url     : https://prove2.me/theorems/e48aabe2-9f2d-4b11-9028-1ee7bda10f17
-- title:
--   Planes of $\Lambda$ exist through every later point of a Reeb trajectory
-- statement:
--   Let $S=H^{-1}(1)\subset\mathbb{R}^4$ be a strictly star-shaped level and $J$ a smooth $d\lambda_0$-compatible complex structure on $\xi$. Let $P=(x,T)$ be a periodic Reeb orbit with $\mu_{CZ}(P)\ge3$ such that $\Lambda(K,P)$ is sequentially compact in $C^\infty_{loc}$ for every compact $K\subset\mathbb{R}^4\setminus\{0\}$ disjoint from the cone $\mathbb{R}\times x(\mathbb{R})$. If $y$ is a Reeb trajectory and $\Lambda(\{y(0)\},P)\ne\emptyset$, then $\Lambda(\{y(t)\},P)\neq\emptyset$ for every $t\ge0$.
--
--   Existence part of the continuation of pages along a trajectory.
--
--   **Formalization Note** $\Lambda(K,P)$ is `embeddedFastPlaneSet H J P K γ`; the compactness hypothesis is `IsSeqCompactCInftyLoc`.
-- source:
--   U. Hryniewicz, Fast finite-energy planes in symplectizations and applications, Trans. Amer. Math. Soc. 364 (2012), 1859-1931, arXiv:0812.4076, Section 7.1

import Definitions.Def_FiniteEnergyPlane_OpenBook

namespace FiniteEnergyPlane

open MeasureTheory Metric Filter Topology
open scoped ContDiff ENNReal Real

/-- Let `P` be a periodic Reeb orbit of Conley–Zehnder index at least `3` such that `Λ(K, P)` is
sequentially compact in `C^∞_loc` for every compact `K ⊂ V 1 \ {0}` disjoint from the cone
`ℝ × x(ℝ)`. If `y` is a Reeb trajectory and `Λ({y 0}, P)` is not empty, then `Λ({y t}, P)` is not
empty for every `t ≥ 0`. -/
theorem embeddedFastPlaneSet_nonempty_of_isReebTrajectory (H : V 1 → ℝ)
    (hH : IsStrictlyStarShapedLevel H) (J : V 1 → V 1 →L[ℝ] V 1) (hJ : IsCompatibleXiStructure H J)
    (P : ReebOrbit H) (hcz : P.IsCZAtLeast 3) (γ : ℝ)
    (hΛ : ∀ K : Set (V 1), IsCompact K → (0 : V 1) ∉ K → (∀ y ∈ K, proj H y ∉ Set.range P.x) →
      IsSeqCompactCInftyLoc (embeddedFastPlaneSet H J P K γ))
    (y : ℝ → V 1) (hy : IsReebTrajectory H y)
    (h0 : (embeddedFastPlaneSet H J P {y 0} γ).Nonempty) (t : ℝ) (ht : 0 ≤ t) :
    (embeddedFastPlaneSet H J P {y t} γ).Nonempty := by
  sorry

end FiniteEnergyPlane
