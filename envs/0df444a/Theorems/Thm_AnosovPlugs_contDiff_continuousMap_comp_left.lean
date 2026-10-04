-- Prove2me | Theorems.Thm_AnosovPlugs_contDiff_continuousMap_comp_left
-- name    : AnosovPlugs.contDiff_continuousMap_comp_left
-- status  : Proved
-- author  : @ebayuser
-- created : 2026-10-04T09:36:33.681849+00:00
-- url     : https://prove2.me/theorems/4cabaf96-d389-41ce-8596-fff4b58b9135
-- title:
--   Post-composition with a C¹ map is a C¹ operator between spaces of continuous maps on a compact space
-- statement:
--   Let $X$ be a compact topological space, let $E$ and $F$ be real normed spaces, and let $v:E\to F$ be a map of class C¹. Write $C(X,E)$ for the space of continuous maps $X\to E$ with the supremum norm. Then the composition operator
--   $$ N_v: C(X,E)\to C(X,F),\qquad N_v(\beta)=v\circ\beta, $$
--   is of class C¹.
--
--   In words: post-composition with a C¹ map is a C¹ map between spaces of continuous functions on a compact space (the composition operator, also called the Nemytskii operator). Its derivative at $\beta$ is $h\mapsto\big(s\mapsto Dv(\beta(s))\,h(s)\big)$. A general fact of analysis, not stated in the paper. In this mission it is a step in the proof of the companion theorem `exists_localFlow_contMDiff_of_isInteriorPoint`. That theorem says that the local flow of a C¹ vector field at an interior point is jointly C¹ in the initial point and the time. The proof of Proposition 1.1 (Section 3.1 of arXiv v1) uses it tacitly. There $X$ is a compact time interval and $N_v$ is the nonlinear part of the Picard operator $\beta\mapsto x+\tau\int_0^{\cdot} v(\beta)$.
--
--   **Formalization Note** $C(X,E)$ is Mathlib's `C(X, E)` (`ContinuousMap`) with the norm that exists for compact $X$. The operator is written `fun β => ⟨v ∘ β, _⟩`, where the second component is the proof that $v\circ\beta$ is continuous. No completeness and no finite dimension is assumed. Mathlib (at the pinned version) has the linear case only (`ContinuousLinearMap.compLeftContinuous`).
-- source:
--   F. Béguin, C. Bonatti, B. Yu, *Building Anosov flows on 3-manifolds*, Geom. Topol. 21 (2017) 1837–1930, https://doi.org/10.2140/gt.2017.21.1837 (arXiv:1408.3951v1). General fact of analysis (differentiability of the composition operator), not stated in the paper; used tacitly in the proof of Proposition 1.1 through differentiable dependence of flows on initial conditions. Mathlib notions: ContinuousMap, ContDiff.

import Mathlib
import Definitions.Def_AnosovPlugs_Gluing

open scoped Manifold ContDiff Topology
open Set

namespace AnosovPlugs

theorem contDiff_continuousMap_comp_left
    {X : Type} [TopologicalSpace X] [CompactSpace X]
    {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (v : E → F) (hv : ContDiff ℝ 1 v) :
    ContDiff ℝ 1 (fun β : C(X, E) => (⟨v ∘ β, hv.continuous.comp β.continuous⟩ : C(X, F))) := by sorry

end AnosovPlugs
