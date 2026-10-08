-- Prove2me | Theorems.Thm_AnosovPlugs_plugGluing_pieces_flowMap_invariant
-- name    : AnosovPlugs.plugGluing_pieces_flowMap_invariant
-- status  : Proved
-- author  : @ebayuser
-- created : 2026-10-04T23:58:20.831989+00:00
-- url     : https://prove2.me/theorems/dc566a7e-2a66-446d-a5bd-98af41fc8654
-- title:
--   The images of the maximal invariant sets of the two plugs are invariant under the time-t maps of the glued vector field
-- statement:
--   Let $(U,X)$ and $(V,Y)$ be plugs: compact Hausdorff smooth 3-manifolds with boundary carrying nonsingular C¹ vector fields transverse to the boundary. Let $T^{out}\subseteq\partial^{out}U$ and $T^{in}\subseteq\partial^{in}V$ be unions of connected components of the exit and entrance boundaries, and let $\varphi:T^{out}\to T^{in}$ be a C¹ diffeomorphism (the mission's `IsBoundaryDiffeo`). Let $(W,Z,i_U,i_V)$ be a plug gluing (the mission's `IsPlugGluing`): $W$ is a compact Hausdorff smooth 3-manifold with boundary, $i_U:U\to W$ and $i_V:V\to W$ are C¹ embeddings with injective derivatives whose images cover $W$ and meet exactly along the seam $i_U(x)=i_V(\varphi(x))$, $x\in T^{out}$, and $Z$ is the vector field on $W$ with $Z\circ i_U=Di_U\circ X$ and $Z\circ i_V=Di_V\circ Y$. The field $Z$ is not assumed to be C¹. We write $\phi^Z_t$ for the time-$t$ map of $Z$, the mission's `flowMap Z t`: it sends $y$ to $\gamma(t)$ for a chosen integral curve $\gamma$ of $Z$ on $[0,t]$ with $\gamma(0)=y$ when one exists (the mission's `FlowDefined Z y t`), and to $y$ otherwise. Let $\Lambda_X$ and $\Lambda_Y$ be the maximal invariant sets of $X$ and $Y$ (the points that lie on an integral curve defined for all times). Then the two pieces are invariant under the time-$t$ maps of $Z$:
--   $$ \phi^Z_t\big(i_U(\Lambda_X)\big)\subseteq i_U(\Lambda_X)\quad\text{and}\quad \phi^Z_t\big(i_V(\Lambda_Y)\big)\subseteq i_V(\Lambda_Y)\qquad\text{for all } t\in\mathbb R. $$
--
--   In words: if $\delta$ is an integral curve of $X$ defined for all times, then $i_U\circ\delta$ is an integral curve of $Z$ defined for all times, and by uniqueness of integral curves of $Z$ (`plugGluing_integralCurveOn_unique`) the time-$t$ map of $Z$ sends $i_U(\delta(0))$ to $i_U(\delta(t))$. It is a step of the mission's proof of Proposition 1.1 (Section 3.1 of arXiv v1, p. 14) that the paper takes for granted. The invariance of the bundles of the two pieces under the flow of $Z$ refers to these maps.
--
--   **Formalization Note** The hypotheses are those of the mission's gluing statements. The proof in the mission uses the plug hypotheses, `hTout`, `hTin` and the hypothesis on $\varphi$ only through the uniqueness theorem `plugGluing_integralCurveOn_unique`. The statement itself needs uniqueness of integral curves of $Z$ only along orbits that stay in the images of the interiors of $U$ and $V$, away from the seam; the hypotheses are kept so that they match the mission's gluing statements. The plugs are not assumed hyperbolic.
-- source:
--   F. Béguin, C. Bonatti, B. Yu, *Building Anosov flows on 3-manifolds*, Geom. Topol. 21 (2017) 1837–1930, https://doi.org/10.2140/gt.2017.21.1837 (arXiv:1408.3951v1). Used tacitly in the proof of Proposition 1.1 (arXiv v1 Section 3.1, p. 14), where the maximal invariant sets of the two plugs are treated as invariant sets of Z. Mission notions: IsPlugGluing, IsPlug, maxInvSet, flowMap; companion theorem plugGluing_integralCurveOn_unique.

import Mathlib
import Definitions.Def_AnosovPlugs_Gluing

open scoped Manifold ContDiff Topology
open Set

namespace AnosovPlugs

theorem plugGluing_pieces_flowMap_invariant
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
    (∀ w ∈ iU '' maxInvSet X, ∀ t : ℝ, flowMap Z t w ∈ iU '' maxInvSet X) ∧
    (∀ w ∈ iV '' maxInvSet Y, ∀ t : ℝ, flowMap Z t w ∈ iV '' maxInvSet Y) := by sorry

end AnosovPlugs
