-- Prove2me | Theorems.Thm_AnosovPlugs_flowMap_eq_of_isMIntegralCurve
-- name    : AnosovPlugs.flowMap_eq_of_isMIntegralCurve
-- status  : Proved
-- author  : @ebayuser
-- created : 2026-10-03T01:18:10.942687+00:00
-- url     : https://prove2.me/theorems/650d877a-ad14-4f21-9202-7e2f7d315bea
-- title:
--   The time-t map of a C¹ vector field agrees with a complete integral curve through interior points
-- statement:
--   Let $M$ be a Hausdorff smooth 3-manifold with boundary (modelled on the closed half-space) and let $X$ be a C¹ vector field on $M$. Let $\gamma:\mathbb R\to M$ be a complete integral curve of $X$ (defined for all times) all of whose points $\gamma(s)$ are interior points of $M$. Then for every real $t$,
--   $$ X^t(\gamma(0)) = \gamma(t), $$
--   where $X^t$ is the time-$t$ map of the (partial) flow of $X$.
--
--   In words: the time-$t$ map is given by the complete integral curve whenever one exists through the interior. This is the uniqueness of integral curves of a C¹ vector field, applied to the mission's definition of the flow; it is a general fact, not stated in the paper. In the formal proof of the parent statement it gives the invariance $X^t(\Lambda_X)\subseteq\Lambda_X$ of the maximal invariant set under the time-$t$ maps.
--
--   **Formalization Note** The time-$t$ map $X^t$ is the mission's `flowMap`: when some integral curve of $X$ through $x$ is defined on the closed time interval between $0$ and $t$, $X^t(x)$ is the value at time $t$ of a chosen such curve; otherwise $X^t(x)=x$. Nothing in the definition asserts that this choice is unique. The statement says that this choice agrees with $\gamma$ when $\gamma$ is a complete integral curve through interior points. The interior hypothesis matches Mathlib's uniqueness theorem `isMIntegralCurveOn_Ioo_eqOn_of_contMDiff`, which is proved for curves through interior points; the statement is expected to hold without it, but that is not asserted. C¹ is the mission's `IsC1VectorField` (the section $x\mapsto(x,X(x))$ of the tangent bundle is C¹).
-- source:
--   F. Béguin, C. Bonatti, B. Yu, *Building Anosov flows on 3-manifolds*, Geom. Topol. 21 (2017) 1837–1930, https://doi.org/10.2140/gt.2017.21.1837 (arXiv:1408.3951v1). A general fact (uniqueness of integral curves of a C¹ vector field), not stated in the paper; used implicitly whenever the paper speaks of the orbit of a point of a maximal invariant set (Definitions 2.1 of arXiv v1, p. 7; proof of Proposition 1.1, p. 14). Mathlib notions: IsMIntegralCurve, isMIntegralCurveOn_Ioo_eqOn_of_contMDiff, ModelWithCorners.IsInteriorPoint; mission notions: flowMap, IsC1VectorField.

import Mathlib
import Definitions.Def_AnosovPlugs_Gluing

open scoped Manifold ContDiff Topology
open Set

namespace AnosovPlugs

theorem flowMap_eq_of_isMIntegralCurve
    {M : Type} [TopologicalSpace M] [ChartedSpace (EuclideanHalfSpace 3) M] [IsManifold I3 ∞ M]
    [T2Space M]
    (X : (x : M) → TangentSpace I3 x) (hX : IsC1VectorField X) (γ : ℝ → M)
    (hγ : IsMIntegralCurve γ X) (hint : ∀ s : ℝ, I3.IsInteriorPoint (γ s)) (t : ℝ) :
    flowMap X t (γ 0) = γ t := by sorry

end AnosovPlugs
