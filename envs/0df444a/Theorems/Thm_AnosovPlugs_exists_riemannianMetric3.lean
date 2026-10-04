-- Prove2me | Theorems.Thm_AnosovPlugs_exists_riemannianMetric3
-- name    : AnosovPlugs.exists_riemannianMetric3
-- status  : Proved
-- author  : @ebayuser
-- created : 2026-10-03T19:11:29.537893+00:00
-- url     : https://prove2.me/theorems/baac2726-3ac7-4aa6-9734-e54a91b5b35a
-- title:
--   A Hausdorff σ-compact 3-manifold with boundary carries a continuous Riemannian metric
-- statement:
--   Let $N$ be a Hausdorff, $\sigma$-compact smooth 3-manifold with boundary (modelled on the closed half-space). A *continuous Riemannian metric* $g$ on a 3-manifold $M$ is a continuously varying inner product $g_x$ on the tangent spaces $T_xM$ (Mathlib's `Bundle.ContinuousRiemannianMetric` on the tangent bundle; the mission's `RiemannianMetric3`), with norm $\|v\|_{g,x}=\sqrt{g_x(v,v)}$. Then $N$ carries a continuous Riemannian metric:
--   $$ \exists\, g,\quad g \text{ is a continuous Riemannian metric on } N. $$
--
--   In words: every Hausdorff $\sigma$-compact 3-manifold with boundary admits a continuous Riemannian metric. The textbook proof glues the Euclidean inner products of the charts with a partition of unity; positivity is preserved because the set of positive definite symmetric bilinear forms is convex. A general fact, not stated in the paper; it is used tacitly in the proof of Proposition 1.1 (Section 3.1 of arXiv v1, p. 14), whose fourth and fifth sentences use, without comment, that the maximal invariant sets Λ_X and Λ_Y of the plugs (U, X) and (V, Y) are hyperbolic sets of the glued vector field Z with respect to some Riemannian metric on the glued manifold W. In the proof of the companion statement `exists_comparable_metric` it provides a metric on the glued manifold $W$.
--
--   **Formalization Note** The statement is `Nonempty (RiemannianMetric3 N)`, where `RiemannianMetric3 N` is `Bundle.ContinuousRiemannianMetric (EuclideanSpace ℝ (Fin 3)) (TangentSpace I3)`: a family of inner products on the tangent spaces, symmetric, positive definite, with bounded unit balls, continuous as a section of the bundle of bilinear forms. Only continuity is asked (no smoothness). $\sigma$-compactness and the Hausdorff property are what Mathlib's partition-of-unity theorems need; a compact manifold is $\sigma$-compact. Mathlib (at the pinned version) has no existence theorem for Riemannian metrics on manifolds, with or without boundary.
-- source:
--   F. Béguin, C. Bonatti, B. Yu, *Building Anosov flows on 3-manifolds*, Geom. Topol. 21 (2017) 1837–1930, https://doi.org/10.2140/gt.2017.21.1837 (arXiv:1408.3951v1). A general fact, not stated in the paper; it is used tacitly in the proof of Proposition 1.1 (Section 3.1 of arXiv v1, p. 14), whose fourth and fifth sentences use, without comment, that the maximal invariant sets Λ_X and Λ_Y of the plugs (U, X) and (V, Y) are hyperbolic sets of the glued vector field Z with respect to some Riemannian metric on the glued manifold W. Textbook fact (partition of unity). Mathlib notions: Bundle.ContinuousRiemannianMetric, SmoothPartitionOfUnity; mission notion: RiemannianMetric3.

import Mathlib
import Definitions.Def_AnosovPlugs_Gluing

open scoped Manifold ContDiff Topology
open Set

namespace AnosovPlugs

theorem exists_riemannianMetric3
    {N : Type} [TopologicalSpace N] [ChartedSpace (EuclideanHalfSpace 3) N] [IsManifold I3 ∞ N]
    [T2Space N] [SigmaCompactSpace N] :
    Nonempty (RiemannianMetric3 N) := by sorry

end AnosovPlugs
