-- Prove2me | Theorems.Thm_FiniteEnergyPlane_exists_mem_embeddedFastPlaneSet_of_isEmbeddedPlane
-- name    : FiniteEnergyPlane.exists_mem_embeddedFastPlaneSet_of_isEmbeddedPlane
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-11-25T10:18:51.179195+00:00
-- url     : https://prove2.me/theorems/bff77b8b-8a5c-4e09-82fa-b68b85280489
-- title:
--   Normalized planes through every point of the projection of an embedded fast plane
-- statement:
--   Let $S=H^{-1}(1)\subset\mathbb{R}^4$ be a strictly star-shaped level and $J$ a smooth $d\lambda_0$-compatible complex structure on $\xi$. Let $u$ be an embedded fast finite-energy plane asymptotic to the periodic Reeb orbit $P=(x,T)$ at $\infty$, let $0<\gamma<T$ and $\zeta\in\mathbb{C}$. Then there is $v\in\Lambda(\{\mathrm{proj}(u(\zeta))\},P)$ with $\mathrm{proj}(v(\mathbb{C}))=\mathrm{proj}(u(\mathbb{C}))$.
--
--   Reusable for replacing an arbitrary embedded fast plane with a member of $\Lambda$ with the same leaf in $S$ and a prescribed base point.
--
--   **Formalization Note** $\Lambda(K,P)$ is `embeddedFastPlaneSet H J P K γ`: embedded fast planes asymptotic to $P$ at $\infty$, with $v(0)\in K$ and $d\lambda$-energy $\gamma$ on $\{|z|>1\}$. The point $(0,q)$ of the symplectization is $q\in S$ itself.
-- source:
--   U. Hryniewicz, Fast finite-energy planes in symplectizations and applications, Trans. Amer. Math. Soc. 364 (2012), 1859-1931, arXiv:0812.4076, Section 7

import Definitions.Def_FiniteEnergyPlane_OpenBook

namespace FiniteEnergyPlane

open MeasureTheory Metric Filter Topology
open scoped ContDiff ENNReal Real

/-- Let `u` be an embedded fast finite-energy plane asymptotic to `P` at `∞`, let `0 < γ < P.T` and
`ζ ∈ ℂ`. There is a plane `v ∈ Λ({proj H (u ζ)}, P)` whose projection to `S` has the same image as
the projection of `u`. -/
theorem exists_mem_embeddedFastPlaneSet_of_isEmbeddedPlane (H : V 1 → ℝ)
    (hH : IsStrictlyStarShapedLevel H)
    (J : V 1 → V 1 →L[ℝ] V 1) (hJ : IsCompatibleXiStructure H J)
    (P : ReebOrbit H) (γ : ℝ) (hγ : 0 < γ) (hγT : γ < P.T) (u : ℂ → V 1)
    (hu : IsFastPlane H J u) (huP : IsNondegenerateEnd H u cylInf P 1) (hue : IsEmbeddedPlane u)
    (ζ : ℂ) :
    ∃ v ∈ embeddedFastPlaneSet H J P {proj H (u ζ)} γ,
      Set.range (fun z => proj H (v z)) = Set.range (fun z => proj H (u z)) := by
  sorry

end FiniteEnergyPlane
