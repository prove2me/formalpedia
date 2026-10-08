-- Prove2me | Theorems.Thm_AnosovPlugs_plugGluing_flowMap_contMDiffOn
-- name    : AnosovPlugs.plugGluing_flowMap_contMDiffOn
-- status  : Proved
-- author  : @ebayuser
-- created : 2026-10-04T20:34:59.006857+00:00
-- url     : https://prove2.me/theorems/641e6f9c-2406-4722-9b0b-0758d1b3affc
-- title:
--   The time-t maps of the glued vector field of a plug gluing are C¹ near its maximal invariant set, also across the seam
-- statement:
--   Let $(U,X)$ and $(V,Y)$ be plugs: compact Hausdorff smooth 3-manifolds with boundary carrying nonsingular C¹ vector fields transverse to the boundary. Let $T^{out}\subseteq\partial^{out}U$ and $T^{in}\subseteq\partial^{in}V$ be unions of connected components of the exit and entrance boundaries, and let $\varphi:T^{out}\to T^{in}$ be a C¹ diffeomorphism (the mission's `IsBoundaryDiffeo`). Let $(W,Z,i_U,i_V)$ be a plug gluing (the mission's `IsPlugGluing`): $W$ is a compact Hausdorff smooth 3-manifold with boundary, $i_U:U\to W$ and $i_V:V\to W$ are C¹ embeddings with injective derivatives whose images cover $W$ and meet exactly along the seam $i_U(x)=i_V(\varphi(x))$, $x\in T^{out}$, and $Z$ is the vector field on $W$ with $Z\circ i_U=Di_U\circ X$ and $Z\circ i_V=Di_V\circ Y$. The field $Z$ is not assumed to be C¹. An *integral curve of a vector field $F$ on a manifold $N$ on a set of times* $S\subseteq\mathbb R$ is a curve $\gamma:\mathbb R\to N$ whose derivative within $S$ at every $u\in S$ is $F(\gamma(u))$ (Mathlib's `IsMIntegralCurveOn`; at the endpoints of an interval the derivative is one-sided). We write $[0,t]$ for the closed interval between $0$ and $t$, in either order (Mathlib's `uIcc 0 t`). We write $\phi^Z_t$ for the time-$t$ map of $Z$, the mission's `flowMap Z t`: it sends $y$ to $\gamma(t)$ for a chosen integral curve $\gamma$ of $Z$ on $[0,t]$ with $\gamma(0)=y$ when one exists (the mission's `FlowDefined Z y t`), and to $y$ otherwise. Then the time-$t$ maps of $Z$ are C¹ near the maximal invariant set: for every point $w$ of the maximal invariant set $\Lambda_Z$ (the points that lie on an integral curve of $Z$ defined for all times), $w$ is an interior point of $W$, and for every $t\in\mathbb R$ there is an open neighbourhood $O$ of $w$ such that the orbit of every $y\in O$ is defined on $[0,t]$ and the time-$t$ map of $Z$ is of class C¹ on $O$:
--   $$ \forall w\in\Lambda_Z:\quad w\in\operatorname{int}W\ \text{ and }\ \forall t\in\mathbb R\ \exists O\ni w \text{ open}:\ \phi^Z_t \text{ is defined and } C^1 \text{ on } O. $$
--
--   In words: $i_U$ and $i_V$ are only C¹, so $Z$ is only continuous on each of the two pieces $i_U(U)$ and $i_V(V)$. On each piece the flow of $Z$ is conjugate by $i_U$ or $i_V$ to the C¹ flow of $X$ or $Y$; no such description is available across the seam $i_U(T^{out})$. The statement says that the flow of $Z$ is C¹ all the same near every orbit that is defined for all times, also when the orbit crosses the seam. It is used in the proof of Proposition 1.1 (Section 3.1 of arXiv v1, p. 14). The fifth sentence of that proof gives a hyperbolic structure to the orbits that cross the seam; the derivatives of the time-$t$ maps along these orbits are part of the definition of a hyperbolic set. The paper takes their existence for granted: footnote 2 states, without proof, that $W$ has a differentiable structure, compatible with those of $U$ and $V$, for which $Z$ is a differentiable vector field.
--
--   The expected proof has three parts, which are companion theorems. At a point of an orbit that is the image of an interior point of $U$ or $V$, the C¹ local flow of $X$ or $Y$ (`exists_localFlow_contMDiff_of_isInteriorPoint`) is transported by the embedding (`localSteps_of_embedding`). At a seam point there is a C¹ flow box (`plugGluing_localSteps_seam`). A compact orbit segment is covered by finitely many such local steps, and the time-$t$ map is their composition, by uniqueness of integral curves of $Z$ (`flowMap_contMDiffOn_of_localSteps` with `plugGluing_integralCurveOn_unique`). A point of a complete orbit is never a boundary point of $W$ (`plugGluing_transverse_boundary` with `normalCoord_nonneg_of_hasMFDerivWithinAt`), and it is never the image of a boundary point of $U$ or $V$ outside the seam (lift the orbit with `integralCurve_lift_of_embedding` and use the transversality of $X$ or $Y$).
--
--   **Formalization Note** The conclusion is `∀ w ∈ maxInvSet Z, I3.IsInteriorPoint w ∧ ∀ t, ∃ O, IsOpen O ∧ w ∈ O ∧ (∀ y ∈ O, FlowDefined Z y t) ∧ ContMDiffOn I3 I3 1 (flowMap Z t) O`. The clause `FlowDefined` is stated because `flowMap` is junk-valued where no integral curve exists. The plugs are not assumed hyperbolic, and no transversality of laminations is assumed. The hypotheses are those of the mission's gluing statements.
-- source:
--   F. Béguin, C. Bonatti, B. Yu, *Building Anosov flows on 3-manifolds*, Geom. Topol. 21 (2017) 1837–1930, https://doi.org/10.2140/gt.2017.21.1837 (arXiv:1408.3951v1). Used tacitly in the proof of Proposition 1.1 (arXiv v1 Section 3.1, p. 14; footnote 2 is attached to the statement of Proposition 1.1, arXiv v1 Section 1, p. 2). Mission notions: IsPlugGluing, IsPlug, maxInvSet, flowMap, FlowDefined; companion theorems flowMap_contMDiffOn_of_localSteps, localSteps_of_embedding, plugGluing_localSteps_seam, plugGluing_integralCurveOn_unique, exists_localFlow_contMDiff_of_isInteriorPoint.

import Mathlib
import Definitions.Def_AnosovPlugs_Gluing

open scoped Manifold ContDiff Topology
open Set

namespace AnosovPlugs

theorem plugGluing_flowMap_contMDiffOn
    {U : Type} [TopologicalSpace U] [ChartedSpace (EuclideanHalfSpace 3) U]
    [IsManifold I3 ∞ U] [T2Space U] [CompactSpace U]
    {V : Type} [TopologicalSpace V] [ChartedSpace (EuclideanHalfSpace 3) V]
    [IsManifold I3 ∞ V] [T2Space V] [CompactSpace V]
    {W : Type} [TopologicalSpace W] [ChartedSpace (EuclideanHalfSpace 3) W]
    [IsManifold I3 ∞ W] [T2Space W] [CompactSpace W]
    (X : (x : U) → TangentSpace I3 x) (Y : (y : V) → TangentSpace I3 y)
    (hX : IsPlug X) (hY : IsPlug Y)
    (Tout : Set U) (Tin : Set V) (hTout : IsUnionOfComponents Tout (outBoundary X))
    (hTin : IsUnionOfComponents Tin (inBoundary Y)) (φ : U → V)
    (hφ : IsBoundaryDiffeo φ Tout Tin)
    (Z : (w : W) → TangentSpace I3 w) (iU : U → W) (iV : V → W)
    (hglue : IsPlugGluing X Y Tout φ Z iU iV) :
    ∀ w ∈ maxInvSet Z, I3.IsInteriorPoint w ∧ ∀ t : ℝ, ∃ O : Set W, IsOpen O ∧ w ∈ O ∧
      (∀ y ∈ O, FlowDefined Z y t) ∧ ContMDiffOn I3 I3 1 (flowMap Z t) O := by sorry

end AnosovPlugs
