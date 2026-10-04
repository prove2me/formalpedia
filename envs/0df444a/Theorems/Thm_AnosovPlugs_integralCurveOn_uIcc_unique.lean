-- Prove2me | Theorems.Thm_AnosovPlugs_integralCurveOn_uIcc_unique
-- name    : AnosovPlugs.integralCurveOn_uIcc_unique
-- status  : Proved
-- author  : @ebayuser
-- created : 2026-10-03T20:57:32.53698+00:00
-- url     : https://prove2.me/theorems/30f09421-621c-465b-8d43-9322c4aa2175
-- title:
--   Integral curves of a C¹ vector field on a 3-manifold with boundary are unique on a closed interval from their starting point, boundary points allowed
-- statement:
--   Let $M$ be a Hausdorff smooth 3-manifold with boundary (modelled on the closed half-space), let $X$ be a C¹ vector field on $M$ and let $t\in\mathbb R$. An *integral curve of $X$ on a set of times* $S\subseteq\mathbb R$ is a curve $\gamma:\mathbb R\to M$ whose derivative within $S$ at every $u\in S$ is $X(\gamma(u))$ (Mathlib's `IsMIntegralCurveOn`; at the endpoints of an interval the derivative is one-sided). We write $[0,t]$ for the closed interval between $0$ and $t$, in either order (Mathlib's `uIcc 0 t`). If $\gamma$ and $\gamma'$ are integral curves of $X$ on $[0,t]$ with $\gamma'(0)=\gamma(0)$, then
--   $$ \gamma'(s)=\gamma(s)\quad\text{for all } s\in[0,t]. $$
--
--   In words: integral curves of a C¹ vector field on a manifold with boundary are determined by their starting point, on a closed time interval in either time direction, also when the curves run along or touch the boundary. The proof reads both curves in the chart at a point of agreement. There the field is C¹ within the closed half-space. The half-space is convex, so the field is locally Lipschitz on it. The uniqueness theorem for Lipschitz ordinary differential equations then applies to solutions that stay in the half-space. The set of agreement times is closed and open in the interval. It is used in the proof of Proposition 1.1 (Section 3.1 of arXiv v1, p. 14; GT 2017 Section 4.1). There it is needed for the glued field $Z$, whose integral curves cross the seam, where the two plugs are glued along their boundaries; the companion theorem `plugGluing_integralCurveOn_unique` derives that case from this one.
--
--   **Formalization Note** Mathlib's uniqueness theorem for integral curves on manifolds (`isMIntegralCurveOn_Ioo_eqOn_of_contMDiff`) requires open intervals and interior points along the first curve. This statement removes both restrictions. The Hausdorff hypothesis makes the set of agreement times closed. C¹ is the mission's `IsC1VectorField`. No compactness is assumed.
-- source:
--   F. Béguin, C. Bonatti, B. Yu, *Building Anosov flows on 3-manifolds*, Geom. Topol. 21 (2017) 1837–1930, https://doi.org/10.2140/gt.2017.21.1837 (arXiv:1408.3951v1). General fact (uniqueness for Lipschitz ODEs within a convex set), used tacitly in footnote 2 and in the proof of Proposition 1.1 (arXiv v1 Section 3.1, GT 2017 Section 4.1). Mathlib notions: IsMIntegralCurveOn, ContDiffWithinAt.exists_lipschitzOnWith, ODE_solution_unique_of_mem_Icc_right, ODE_solution_unique_of_mem_Icc_left; mission notion: IsC1VectorField.

import Mathlib
import Definitions.Def_AnosovPlugs_Gluing

open scoped Manifold ContDiff Topology
open Set

namespace AnosovPlugs

theorem integralCurveOn_uIcc_unique
    {M : Type} [TopologicalSpace M] [ChartedSpace (EuclideanHalfSpace 3) M] [IsManifold I3 ∞ M]
    [T2Space M]
    (X : (x : M) → TangentSpace I3 x) (hX : IsC1VectorField X) (γ γ' : ℝ → M) (t : ℝ)
    (hγ : IsMIntegralCurveOn γ X (uIcc 0 t)) (hγ' : IsMIntegralCurveOn γ' X (uIcc 0 t))
    (h0 : γ' 0 = γ 0) :
    ∀ s ∈ uIcc 0 t, γ' s = γ s := by sorry

end AnosovPlugs
