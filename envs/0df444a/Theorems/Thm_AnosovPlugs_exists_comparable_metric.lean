-- Prove2me | Theorems.Thm_AnosovPlugs_exists_comparable_metric
-- name    : AnosovPlugs.exists_comparable_metric
-- status  : Proved
-- author  : @ebayuser
-- created : 2026-10-03T01:18:37.821531+00:00
-- url     : https://prove2.me/theorems/049d4a3c-2bc2-40ea-8655-421ab6c6d644
-- title:
--   A continuous Riemannian metric comparable along a C¹ immersion of a compact manifold
-- statement:
--   Let $M$ and $N$ be compact smooth 3-manifolds with boundary (modelled on the closed half-space; $M$ and $N$ Hausdorff), and let $i:M\to N$ be a C¹ map whose derivative $Di_x$ is injective at every point $x\in M$. Let $g$ be a continuous Riemannian metric on $M$ (a continuously varying inner product on the tangent spaces). Then there are a continuous Riemannian metric $g'$ on $N$ and constants $c_1,c_2>0$ such that
--   $$ c_1\,\|v\|_{g,x}\ \le\ \|Di_x v\|_{g',i(x)}\ \le\ c_2\,\|v\|_{g,x}\quad\text{for every } x\in M \text{ and } v\in T_xM. $$
--
--   In words: there is a continuous Riemannian metric on $N$ that is comparable, along the immersion $i$, with the given metric on $M$ (any continuous metric on $N$ has this property, but only existence is asserted); the constants exist because the unit sphere bundle of $M$ is compact and $Di_x$ is injective. This is a general fact, not stated in the paper; in the proof of Proposition 1.1 it allows the exponential estimates of the hyperbolic structures of $\Lambda_X$ and $\Lambda_Y$, written with metrics on $U$ and $V$, to be rewritten with one metric on $W$.
--
--   **Formalization Note** A continuous Riemannian metric is the mission's `RiemannianMetric3` (Mathlib's `Bundle.ContinuousRiemannianMetric` on the tangent bundle), and $\|v\|_{g,x}=\sqrt{g_x(v,v)}$. The statement asserts the existence of $g'$: Mathlib (at the pinned version) has no existence theorem for continuous Riemannian metrics on manifolds with boundary, so this is part of what is left open. No relation between $i$ and vector fields is assumed; $i$ need not be injective or an embedding.
-- source:
--   F. Béguin, C. Bonatti, B. Yu, *Building Anosov flows on 3-manifolds*, Geom. Topol. 21 (2017) 1837–1930, https://doi.org/10.2140/gt.2017.21.1837 (arXiv:1408.3951v1). A general fact, not stated in the paper; used implicitly in the proof of Proposition 1.1 (Section 3.1 of arXiv v1, p. 14) to express the hyperbolic structures of Λ_X and Λ_Y with a metric on W. Mathlib notions: Bundle.ContinuousRiemannianMetric, mfderiv; mission notion: RiemannianMetric3.

import Mathlib
import Definitions.Def_AnosovPlugs_Gluing

open scoped Manifold ContDiff Topology
open Set

namespace AnosovPlugs

theorem exists_comparable_metric
    {M : Type} [TopologicalSpace M] [ChartedSpace (EuclideanHalfSpace 3) M] [IsManifold I3 ∞ M]
    [T2Space M] [CompactSpace M]
    {N : Type} [TopologicalSpace N] [ChartedSpace (EuclideanHalfSpace 3) N] [IsManifold I3 ∞ N]
    [T2Space N] [CompactSpace N]
    (i : M → N) (hi : ContMDiff I3 I3 1 i) (hinj : ∀ x, Function.Injective (mfderiv I3 I3 i x))
    (g : RiemannianMetric3 M) :
    ∃ g' : RiemannianMetric3 N, ∃ c₁ c₂ : ℝ, 0 < c₁ ∧ 0 < c₂ ∧
      ∀ (x : M) (v : TangentSpace I3 x),
        c₁ * g.norm x v ≤ g'.norm (i x) (mfderiv I3 I3 i x v) ∧
        g'.norm (i x) (mfderiv I3 I3 i x v) ≤ c₂ * g.norm x v := by sorry

end AnosovPlugs
