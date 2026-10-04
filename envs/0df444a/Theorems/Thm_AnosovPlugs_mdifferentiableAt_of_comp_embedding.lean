-- Prove2me | Theorems.Thm_AnosovPlugs_mdifferentiableAt_of_comp_embedding
-- name    : AnosovPlugs.mdifferentiableAt_of_comp_embedding
-- status  : Proved
-- author  : @ebayuser
-- created : 2026-10-03T01:17:42.010822+00:00
-- url     : https://prove2.me/theorems/36ffb871-bf3a-4725-8db5-d64b4a5e1014
-- title:
--   Differentiability transfers through a C¹ embedding with injective derivative at an interior point whose image is a neighbourhood
-- statement:
--   Let $M$, $N$ and $P$ be smooth 3-manifolds with boundary (modelled on the closed half-space), let $i:M\to N$ be a C¹ map that is a topological embedding, and let $x\in M$ be an interior point of $M$ at which the derivative $Di_x$ is injective. Assume that the image $i(M)$ is a neighbourhood of $i(x)$ in $N$. Let $f:N\to P$ be any map. If $f\circ i$ is differentiable at $x$, then
--   $$ f \text{ is differentiable at } i(x). $$
--
--   In words: at such a point $i$ is a local C¹ diffeomorphism onto a neighbourhood of $i(x)$, so $f=(f\circ i)\circ i^{-1}$ near $i(x)$. This is a general fact, not stated in the paper; it is the differentiability step behind footnote 2 (the differentiable structure of $W=U\sqcup_\varphi V$ is compatible with those of $U$ and $V$ by restriction), and it is used to transfer differentiability of the time-$t$ maps of the glued field from the pieces to $W$.
--
--   **Formalization Note** "Differentiable at a point" is Mathlib's `MDifferentiableAt`: continuity at the point and differentiability of the chart representative within the model half-space. The hypothesis that $i(M)$ is a neighbourhood of $i(x)$ is assumed; it also follows from the other hypotheses by the inverse function theorem ($x$ is interior and $Di_x$ is a linear isomorphism), and the embedding hypothesis is then not needed either. No compactness is assumed.
-- source:
--   F. Béguin, C. Bonatti, B. Yu, *Building Anosov flows on 3-manifolds*, Geom. Topol. 21 (2017) 1837–1930, https://doi.org/10.2140/gt.2017.21.1837 (arXiv:1408.3951v1). A general fact about C¹ embeddings, not stated in the paper; footnote 2 of Section 1 (p. 2) of arXiv v1 gives the setting. Mathlib notions: MDifferentiableAt, ModelWithCorners.IsInteriorPoint, Topology.IsEmbedding, mfderiv.

import Mathlib
import Definitions.Def_AnosovPlugs_Gluing

open scoped Manifold ContDiff Topology
open Set

namespace AnosovPlugs

theorem mdifferentiableAt_of_comp_embedding
    {M : Type} [TopologicalSpace M] [ChartedSpace (EuclideanHalfSpace 3) M] [IsManifold I3 ∞ M]
    {N : Type} [TopologicalSpace N] [ChartedSpace (EuclideanHalfSpace 3) N] [IsManifold I3 ∞ N]
    {P : Type} [TopologicalSpace P] [ChartedSpace (EuclideanHalfSpace 3) P] [IsManifold I3 ∞ P]
    (i : M → N) (hi : ContMDiff I3 I3 1 i) (hemb : Topology.IsEmbedding i) (x : M)
    (hx : I3.IsInteriorPoint x) (hinj : Function.Injective (mfderiv I3 I3 i x))
    (hnhds : range i ∈ 𝓝 (i x)) (f : N → P) (hf : MDifferentiableAt I3 I3 (f ∘ i) x) :
    MDifferentiableAt I3 I3 f (i x) := by sorry

end AnosovPlugs
