-- Prove2me | Theorems.Thm_AnosovPlugs_flowMap_flowProperty_of_regularity
-- name    : AnosovPlugs.flowMap_flowProperty_of_regularity
-- status  : Proved
-- author  : @ebayuser
-- created : 2026-10-04T23:57:59.726392+00:00
-- url     : https://prove2.me/theorems/3f5d2dda-9556-4272-a5f5-582751d18a80
-- title:
--   With unique integral curves and C¹ time-t maps, the time-t maps form a flow on the maximal invariant set and their derivatives satisfy the chain rule
-- statement:
--   Let $N$ be a smooth 3-manifold with boundary (modelled on the closed half-space) and let $Z$ be a vector field on $N$; no regularity of $Z$ is assumed. An *integral curve of a vector field $Z$ on a manifold $N$ on a set of times* $S\subseteq\mathbb R$ is a curve $\gamma:\mathbb R\to N$ whose derivative within $S$ at every $u\in S$ is $Z(\gamma(u))$ (Mathlib's `IsMIntegralCurveOn`; at the endpoints of an interval the derivative is one-sided). We write $[0,t]$ for the closed interval between $0$ and $t$, in either order (Mathlib's `uIcc 0 t`). We write $\phi^Z_t$ for the time-$t$ map of $Z$, the mission's `flowMap Z t`: it sends $y$ to $\gamma(t)$ for a chosen integral curve $\gamma$ of $Z$ on $[0,t]$ with $\gamma(0)=y$ when one exists (the mission's `FlowDefined Z y t`), and to $y$ otherwise. We write $D\phi^Z_t(w)$ for the derivative of $\phi^Z_t$ at $w$ (Mathlib's `mfderiv`). Assume:
--   - (uniqueness) for every $t$, two integral curves of $Z$ on $[0,t]$ with the same starting point are equal on $[0,t]$;
--   - (regularity) for every point $w$ of the maximal invariant set $\Lambda_Z$ (the points that lie on an integral curve of $Z$ defined for all times), $w$ is an interior point, and for every $t\in\mathbb R$ there is an open neighbourhood $O$ of $w$ such that the orbit of every $y\in O$ is defined on $[0,t]$ and $\phi^Z_t$ is of class C¹ on $O$.
--
--   Then for every $w\in\Lambda_Z$:
--   1. $\phi^Z_t(w)\in\Lambda_Z$ for all $t$;
--   2. $\phi^Z_t(\phi^Z_s(w))=\phi^Z_{s+t}(w)$ for all $s,t$;
--   3. $D\phi^Z_0(w)=\mathrm{id}$;
--   4. (chain rule) $D\phi^Z_{s+t}(w)=D\phi^Z_t(\phi^Z_s(w))\circ D\phi^Z_s(w)$ for all $s,t$;
--   5. (the field is invariant) $D\phi^Z_t(w)\,Z(w)=Z(\phi^Z_t(w))$ for all $t$.
--   $$ \phi^Z_t\circ\phi^Z_s=\phi^Z_{s+t}\ \text{ on } \Lambda_Z,\qquad D\phi^Z_{s+t}(w)=D\phi^Z_t(\phi^Z_s(w))\circ D\phi^Z_s(w),\qquad D\phi^Z_t(w)\,Z(w)=Z(\phi^Z_t(w)). $$
--
--   In words: on its maximal invariant set, the junk-valued time-$t$ map behaves as a flow, and its derivatives satisfy the chain rule and preserve the field. The group law holds on a neighbourhood of $w$, by uniqueness and the regularity hypothesis, and this gives the chain rule. It is a step of the mission's proof of Proposition 1.1 (Section 3.1 of arXiv v1, p. 14) that the paper takes for granted. There $Z$ is the glued field of a plug gluing, which is not assumed to be C¹; the two hypotheses are the conclusions of `plugGluing_integralCurveOn_unique` and `plugGluing_flowMap_contMDiffOn`.
--
--   **Formalization Note** The derivative is Mathlib's `mfderiv I3 I3 (flowMap Z t) w`; all tangent spaces are $\mathbb R^3$ in the chart at the base point, so the composition in item 4 is a composition of linear maps of $\mathbb R^3$. Items 3 and 4 are stated on vectors $v$. The regularity hypothesis is the verbatim conclusion of `plugGluing_flowMap_contMDiffOn`; its clause on interior points is part of that text. No Hausdorff and no compactness hypothesis is assumed. Item 3 holds at every point of $N$ with no hypothesis, because `flowMap Z 0` is the identity.
-- source:
--   F. Béguin, C. Bonatti, B. Yu, *Building Anosov flows on 3-manifolds*, Geom. Topol. 21 (2017) 1837–1930, https://doi.org/10.2140/gt.2017.21.1837 (arXiv:1408.3951v1). General fact (group law and chain rule for the time-t maps), used tacitly in the proof of Proposition 1.1 (arXiv v1 Section 3.1, p. 14). Mathlib notions: IsMIntegralCurveOn, mfderiv; mission notions: flowMap, FlowDefined, maxInvSet; companion theorems plugGluing_integralCurveOn_unique, plugGluing_flowMap_contMDiffOn.

import Mathlib
import Definitions.Def_AnosovPlugs_Gluing

open scoped Manifold ContDiff Topology
open Set

namespace AnosovPlugs

theorem flowMap_flowProperty_of_regularity
    {N : Type} [TopologicalSpace N] [ChartedSpace (EuclideanHalfSpace 3) N] [IsManifold I3 ∞ N]
    (Z : (w : N) → TangentSpace I3 w)
    (huniq : ∀ (γ γ' : ℝ → N) (t : ℝ), IsMIntegralCurveOn γ Z (uIcc 0 t) → IsMIntegralCurveOn γ' Z (uIcc 0 t) →
        γ' 0 = γ 0 → ∀ s ∈ uIcc 0 t, γ' s = γ s)
    (hreg : ∀ w ∈ maxInvSet Z, I3.IsInteriorPoint w ∧ ∀ t : ℝ, ∃ O : Set N, IsOpen O ∧ w ∈ O ∧
        (∀ y ∈ O, FlowDefined Z y t) ∧ ContMDiffOn I3 I3 1 (flowMap Z t) O) :
    ∀ w ∈ maxInvSet Z,
      (∀ t : ℝ, flowMap Z t w ∈ maxInvSet Z) ∧
      (∀ s t : ℝ, flowMap Z t (flowMap Z s w) = flowMap Z (s + t) w) ∧
      (∀ v : TangentSpace I3 w, mfderiv I3 I3 (flowMap Z 0) w v = v) ∧
      (∀ (s t : ℝ) (v : TangentSpace I3 w), mfderiv I3 I3 (flowMap Z (s + t)) w v =
        mfderiv I3 I3 (flowMap Z t) (flowMap Z s w) (mfderiv I3 I3 (flowMap Z s) w v)) ∧
      (∀ t : ℝ, mfderiv I3 I3 (flowMap Z t) w (Z w) = Z (flowMap Z t w)) := by sorry

end AnosovPlugs
