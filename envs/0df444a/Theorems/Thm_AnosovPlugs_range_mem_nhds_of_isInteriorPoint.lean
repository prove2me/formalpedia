-- Prove2me | Theorems.Thm_AnosovPlugs_range_mem_nhds_of_isInteriorPoint
-- name    : AnosovPlugs.range_mem_nhds_of_isInteriorPoint
-- status  : Proved
-- author  : @ebayuser
-- created : 2026-10-03T08:58:38.205078+00:00
-- url     : https://prove2.me/theorems/d5f0301c-7dfa-46e0-afaa-115757a91b93
-- title:
--   The image of a C¹ map between 3-manifolds is a neighbourhood of the image of an interior point where the derivative is injective
-- statement:
--   Let $M$ and $N$ be smooth 3-manifolds with boundary (modelled on the closed half-space), let $i:M\to N$ be a C¹ map, and let $x\in M$ be an interior point of $M$ at which the derivative $Di_x$ is injective. Then the image $i(M)$ is a neighbourhood of $i(x)$ in $N$:
--   $$ i(M)\in\mathcal N(i(x)). $$
--
--   In words: if a C¹ map between 3-manifolds has an invertible derivative at an interior point, then its image contains a neighbourhood of the image of that point. This is the inverse function theorem read in charts. A general fact, not stated in the paper; it is one of the facts behind footnote 2 of Section 1 (p. 2 of arXiv v1: the differentiable structure on W is compatible with those of U and V by restriction) and behind the fourth and fifth sentences of the proof of Proposition 1.1 (Section 3.1 of arXiv v1, p. 14), which state without proof that Λ_Z contains Λ_X and Λ_Y (through the inclusions) and use, without comment, that Λ_X and Λ_Y are hyperbolic sets of Z. In the proof of the companion statement `plugGluing_local_conjugacy` it shows that $i_U(U)$ is a neighbourhood of $i_U(x)$ for $x$ in the maximal invariant set $\Lambda_X$, which lies in the interior of $U$.
--
--   **Formalization Note** No embedding, injectivity, Hausdorff or compactness hypothesis is assumed; $i$ is only C¹ with $Di_x$ injective (hence a linear isomorphism of $\mathbb R^3$) at the one point $x$. Mathlib (at the pinned version) has no inverse function theorem on manifolds, so the proof goes through the chart representative and Mathlib's `HasStrictFDerivAt.map_nhds_eq_of_equiv`.
-- source:
--   F. Béguin, C. Bonatti, B. Yu, *Building Anosov flows on 3-manifolds*, Geom. Topol. 21 (2017) 1837–1930, https://doi.org/10.2140/gt.2017.21.1837 (arXiv:1408.3951v1). A general fact, not stated in the paper; it is one of the facts behind footnote 2 of Section 1 (p. 2 of arXiv v1: the differentiable structure on W is compatible with those of U and V by restriction) and behind the fourth and fifth sentences of the proof of Proposition 1.1 (Section 3.1 of arXiv v1, p. 14), which state without proof that Λ_Z contains Λ_X and Λ_Y (through the inclusions) and use, without comment, that Λ_X and Λ_Y are hyperbolic sets of Z. Mathlib notions: ModelWithCorners.IsInteriorPoint, mfderiv, Filter.nhds.

import Mathlib
import Definitions.Def_AnosovPlugs_Gluing

open scoped Manifold ContDiff Topology
open Set

namespace AnosovPlugs

theorem range_mem_nhds_of_isInteriorPoint
    {M : Type} [TopologicalSpace M] [ChartedSpace (EuclideanHalfSpace 3) M] [IsManifold I3 ∞ M]
    {N : Type} [TopologicalSpace N] [ChartedSpace (EuclideanHalfSpace 3) N] [IsManifold I3 ∞ N]
    (i : M → N) (hi : ContMDiff I3 I3 1 i) (x : M) (hx : I3.IsInteriorPoint x)
    (hinj : Function.Injective (mfderiv I3 I3 i x)) :
    range i ∈ 𝓝 (i x) := by sorry

end AnosovPlugs
