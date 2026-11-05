-- Prove2me | Theorems.Thm_FiniteEnergyPlane_exists_trajectory_return
-- name    : FiniteEnergyPlane.exists_trajectory_return
-- status  : Open
-- author  : @Mazecto
-- created : 2026-11-04T15:48:54.985114+00:00
-- url     : https://prove2.me/theorems/fda6eff2-16bb-4eef-8d62-fcdfee8068ba
-- title:
--   A Reeb trajectory that returns to a leaf
-- statement:
--   Let $S=H^{-1}(1)\subset\mathbb{R}^4$ be a strictly star-shaped level, $J$ a smooth $d\lambda_0$-compatible complex structure on $\xi$, and $P=(x,T_P)$ a periodic Reeb orbit with $\mu_{CZ}(P)\ge3$ ($P$ may be degenerate unless stated otherwise). Let $0<\gamma<T_P$ be such that $\Lambda(K,P)$ is sequentially compact in $C^\infty_{loc}(\mathbb{C},\mathbb{R}^4)$ for every compact $K\subset\mathbb{R}^4\setminus\{0\}$ with $K\cap(\mathbb{R}\times x(\mathbb{R}))=\emptyset$. If there is an embedded fast finite-energy plane asymptotic to $P$ at $\infty$, then there are a Reeb trajectory $y$, a plane $v\in\Lambda(\{y(0)\},P)$ and $\tau>0$ with $y(\tau)\in\mathrm{proj}(v(\mathbb{C}))$.
--
--   **Formalization Note** The hypothesis on $\Lambda(K,P)$ is exactly the conclusion of `isSeqCompact_embeddedFastPlaneSet` for the same $\gamma$, quantified over $K$; the cylinder $\mathbb{R}\times x(\mathbb{R})$ is the cone $\{y\neq0:\mathrm{proj}(y)\in x(\mathbb{R})\}$. $\mu_{CZ}(P)\ge3$ is `P.IsCZAtLeast 3`, the index of the linearized flow along $P$ in the global frame of $\xi$. Hryniewicz writes $\mu(\tilde u)=k\ge3$ and restricts to $\Lambda_k$; on a strictly star-shaped level $\xi$ has a global frame, which extends over every capping disk, so the index depends only on $P$, $\Lambda_k=\Lambda$, and the condition is not restated. Hryniewicz uses a return of the trajectory to the leaf of the given plane $\tilde u_0$ through a suitable point; here the leaf is only required to exist.
-- source:
--   U. Hryniewicz, Fast finite-energy planes in symplectizations and applications, Trans. Amer. Math. Soc. 364 (2012), 1859–1931, arXiv:0812.4076, Section 7.2.1 (variant: the statement asserts existence of some trajectory and leaf)

import Definitions.Def_FiniteEnergyPlane_OpenBook

namespace FiniteEnergyPlane

open MeasureTheory Metric Filter Topology
open scoped ContDiff ENNReal Real

/-- Hryniewicz (Trans. AMS 2012), § 7.2.1 (variant). Let `P` be a periodic Reeb orbit of
Conley–Zehnder index at least `3`, `0 < γ < P.T`, and suppose `Λ(K, P)` is sequentially compact in
`C^∞_loc` for every compact `K ⊂ V 1 \ {0}` disjoint from the cone `ℝ × x(ℝ)`. If there is an
embedded fast finite-energy plane asymptotic to `P` at `∞`, then there are a Reeb trajectory `y`, a
plane `v ∈ Λ({y 0}, P)` and `τ > 0` such that `y τ` lies in the image of `proj H ∘ v`. -/
theorem exists_trajectory_return (H : V 1 → ℝ) (hH : IsStrictlyStarShapedLevel H)
    (J : V 1 → V 1 →L[ℝ] V 1) (hJ : IsCompatibleXiStructure H J)
    (P : ReebOrbit H) (hcz : P.IsCZAtLeast 3) (γ : ℝ) (hγ : 0 < γ) (hγT : γ < P.T)
    (hΛ : ∀ K : Set (V 1), IsCompact K → (0 : V 1) ∉ K → (∀ y ∈ K, proj H y ∉ Set.range P.x) →
      IsSeqCompactCInftyLoc (embeddedFastPlaneSet H J P K γ))
    (u₀ : ℂ → V 1) (hu₀ : IsFastPlane H J u₀) (hu₀P : IsNondegenerateEnd H u₀ cylInf P 1)
    (hu₀e : IsEmbeddedPlane u₀) :
    ∃ y : ℝ → V 1, IsReebTrajectory H y ∧ ∃ v ∈ embeddedFastPlaneSet H J P {y 0} γ,
      ∃ τ > 0, y τ ∈ Set.range (fun z => proj H (v z)) := by
  sorry

end FiniteEnergyPlane
