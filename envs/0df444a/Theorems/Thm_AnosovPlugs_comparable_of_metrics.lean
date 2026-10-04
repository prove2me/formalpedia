-- Prove2me | Theorems.Thm_AnosovPlugs_comparable_of_metrics
-- name    : AnosovPlugs.comparable_of_metrics
-- status  : Proved
-- author  : @ebayuser
-- created : 2026-10-03T19:11:49.990557+00:00
-- url     : https://prove2.me/theorems/50169df0-9977-4f8e-a63a-a047f689de64
-- title:
--   Along a C¹ immersion of a compact 3-manifold, two continuous Riemannian metrics are uniformly comparable
-- statement:
--   Let $M$ be a compact smooth 3-manifold with boundary and $N$ a smooth 3-manifold with boundary (both modelled on the closed half-space), let $i:M\to N$ be a C¹ map whose derivative $Di_x$ is injective at every $x\in M$, and let $g$ and $g'$ be continuous Riemannian metrics on $M$ and $N$. A *continuous Riemannian metric* $g$ on a 3-manifold $M$ is a continuously varying inner product $g_x$ on the tangent spaces $T_xM$ (Mathlib's `Bundle.ContinuousRiemannianMetric` on the tangent bundle; the mission's `RiemannianMetric3`), with norm $\|v\|_{g,x}=\sqrt{g_x(v,v)}$. Then there are constants $c_1,c_2>0$ such that for every $x\in M$ and every $v\in T_xM$,
--   $$ c_1\,\|v\|_{g,x} \le \|Di_x(v)\|_{g',i(x)} \le c_2\,\|v\|_{g,x}. $$
--
--   In words: along a C¹ immersion of a compact manifold, any two continuous Riemannian metrics are uniformly comparable. The textbook proof bounds the two continuous positive functions $(x,v)\mapsto\|Di_x v\|_{g'}/\|v\|_g$ and its inverse on the compact unit sphere bundle of $M$; injectivity of $Di_x$ makes the numerator positive. A general fact, not stated in the paper; it is used tacitly in the proof of Proposition 1.1 (Section 3.1 of arXiv v1, p. 14), whose fourth and fifth sentences use, without comment, that the maximal invariant sets Λ_X and Λ_Y of the plugs (U, X) and (V, Y) are hyperbolic sets of the glued vector field Z with respect to some Riemannian metric on the glued manifold W. In the proof of the companion statement `exists_comparable_metric` it is applied to the metric of the hyperbolic structure on $U$ and to any continuous metric on $W$.
--
--   **Formalization Note** No Hausdorff hypothesis and no compactness of $N$ is assumed; compactness of $M$ is what makes the constants uniform. The norms are the mission's `RiemannianMetric3.norm`, that is $\sqrt{g_x(v,v)}$, and $Di_x$ is Mathlib's `mfderiv I3 I3 i x`. C¹ is Mathlib's `ContMDiff I3 I3 1`.
-- source:
--   F. Béguin, C. Bonatti, B. Yu, *Building Anosov flows on 3-manifolds*, Geom. Topol. 21 (2017) 1837–1930, https://doi.org/10.2140/gt.2017.21.1837 (arXiv:1408.3951v1). A general fact, not stated in the paper; it is used tacitly in the proof of Proposition 1.1 (Section 3.1 of arXiv v1, p. 14), whose fourth and fifth sentences use, without comment, that the maximal invariant sets Λ_X and Λ_Y of the plugs (U, X) and (V, Y) are hyperbolic sets of the glued vector field Z with respect to some Riemannian metric on the glued manifold W. Textbook fact (compactness of the unit sphere bundle). Mathlib notions: mfderiv, ContMDiff; mission notions: RiemannianMetric3, RiemannianMetric3.norm.

import Mathlib
import Definitions.Def_AnosovPlugs_Gluing

open scoped Manifold ContDiff Topology
open Set

namespace AnosovPlugs

theorem comparable_of_metrics
    {M : Type} [TopologicalSpace M] [ChartedSpace (EuclideanHalfSpace 3) M] [IsManifold I3 ∞ M]
    [CompactSpace M]
    {N : Type} [TopologicalSpace N] [ChartedSpace (EuclideanHalfSpace 3) N] [IsManifold I3 ∞ N]
    (i : M → N) (hi : ContMDiff I3 I3 1 i) (hinj : ∀ x, Function.Injective (mfderiv I3 I3 i x))
    (g : RiemannianMetric3 M) (g' : RiemannianMetric3 N) :
    ∃ c₁ c₂ : ℝ, 0 < c₁ ∧ 0 < c₂ ∧
      ∀ (x : M) (v : TangentSpace I3 x),
        c₁ * g.norm x v ≤ g'.norm (i x) (mfderiv I3 I3 i x v) ∧
        g'.norm (i x) (mfderiv I3 I3 i x v) ≤ c₂ * g.norm x v := by sorry

end AnosovPlugs
