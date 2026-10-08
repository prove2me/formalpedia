-- Prove2me | Theorems.Thm_AnosovPlugs_plugGluing_localSteps_seam
-- name    : AnosovPlugs.plugGluing_localSteps_seam
-- status  : Proved
-- author  : @ebayuser
-- created : 2026-10-04T20:35:57.511994+00:00
-- url     : https://prove2.me/theorems/94e37760-80d1-4c57-a3d1-d7b56ebe54a4
-- title:
--   The glued vector field of a plug gluing has C¹ short-time flow maps near every seam point in the interior
-- statement:
--   Let $(U,X)$ and $(V,Y)$ be plugs: compact Hausdorff smooth 3-manifolds with boundary carrying nonsingular C¹ vector fields transverse to the boundary. Let $T^{out}\subseteq\partial^{out}U$ and $T^{in}\subseteq\partial^{in}V$ be unions of connected components of the exit and entrance boundaries, and let $\varphi:T^{out}\to T^{in}$ be a C¹ diffeomorphism (the mission's `IsBoundaryDiffeo`). Let $(W,Z,i_U,i_V)$ be a plug gluing (the mission's `IsPlugGluing`): $W$ is a compact Hausdorff smooth 3-manifold with boundary, $i_U:U\to W$ and $i_V:V\to W$ are C¹ embeddings with injective derivatives whose images cover $W$ and meet exactly along the seam $i_U(x)=i_V(\varphi(x))$, $x\in T^{out}$, and $Z$ is the vector field on $W$ with $Z\circ i_U=Di_U\circ X$ and $Z\circ i_V=Di_V\circ Y$. The field $Z$ is not assumed to be C¹. An *integral curve of a vector field $F$ on a manifold $N$ on a set of times* $S\subseteq\mathbb R$ is a curve $\gamma:\mathbb R\to N$ whose derivative within $S$ at every $u\in S$ is $F(\gamma(u))$ (Mathlib's `IsMIntegralCurveOn`; at the endpoints of an interval the derivative is one-sided). We write $[0,t]$ for the closed interval between $0$ and $t$, in either order (Mathlib's `uIcc 0 t`). A vector field $F$ on a 3-manifold $N$ has *local C¹ step maps at a point* $p$ if there are $\varepsilon>0$ and an open neighbourhood $O$ of $p$ such that for every $h$ with $|h|\le\varepsilon$ there is a map $f_h:N\to N$ of class C¹ on $O$ with this property: every $y\in O$ is the starting point of an integral curve $\eta$ of $F$ on $[0,h]$ with $\eta(h)=f_h(y)$. Then at every seam point that is an interior point of $W$ the glued field has local C¹ step maps:
--   $$ \forall x\in T^{out}:\quad i_U(x)\in\operatorname{int}W\ \Longrightarrow\ Z \text{ has local } C^1 \text{ step maps at } i_U(x). $$
--
--   In words: the short-time flow maps of $Z$ are C¹ near a seam point, although $Z$ is only continuous: on each side of the seam its flow is conjugate to the C¹ flow of $X$ or $Y$. The expected proof is a flow box. Write $\phi^X_\tau(s)$ for the point at time $\tau$ of the integral curve of $X$ through $s$; for $s\in T^{out}$ near $x$ and $-\delta\le\tau\le0$ it exists, stays in $U$ and is unique. Define $\phi^Y_\tau(s')$ in the same way for $s'\in T^{in}$ and $0\le\tau\le\delta$. For boundary points $s\in T^{out}$ near $x$ put $\Theta(s,\tau)=i_U(\phi^X_\tau(s))$ for $\tau\le0$ and $\Theta(s,\tau)=i_V(\phi^Y_\tau(\varphi(s)))$ for $\tau\ge0$. The two formulas agree for $\tau=0$ because $i_U=i_V\circ\varphi$ on $T^{out}$. Their derivatives agree there: along $T^{out}$ for the same reason, and in the direction of $\tau$ because $Di_U(X)=Z=Di_V(Y)$ at seam points. So $\Theta$ is C¹, and by the inverse function theorem it is a C¹ diffeomorphism from a neighbourhood of $(x,0)$ onto a neighbourhood of $i_U(x)$. In these coordinates the integral curves of $Z$ are the lines $\tau\mapsto(s,\tau)$, and the step map is the translation $f_h=\Theta\circ(\tau\mapsto\tau+h)\circ\Theta^{-1}$. It is a step of the mission's proof of the C¹ regularity that the proof of Proposition 1.1 (Section 3.1 of arXiv v1, p. 14) takes for granted. The statement is the part of the C¹ regularity of the flow of $Z$ that concerns the seam; the paper does not state it (footnote 2, attached to the statement of Proposition 1.1 on p. 2, states without proof that $W$ has a differentiable structure, compatible with those of $U$ and $V$, for which $Z$ is a differentiable vector field).
--
--   **Formalization Note** The hypothesis that $i_U(x)$ is an interior point of $W$ is expected to hold for every $x\in T^{out}$; it is assumed because a proof of it is not in the mission. For points of complete orbits it follows from `plugGluing_transverse_boundary` and `normalCoord_nonneg_of_hasMFDerivWithinAt`. The expected proof uses facts that Mathlib (at the pinned version) does not have: a flow of a C¹ field up to the boundary (through a C¹ extension of the field across the boundary in a chart), and the fact that a map that is C¹ on two closed half-spaces, with equal values and derivatives on the common plane, is C¹. It also uses that $T^{out}$ is open in $\partial U$ (a union of components of the open subset $\partial^{out}U$ of the surface $\partial U$). The plugs are not assumed hyperbolic.
-- source:
--   F. Béguin, C. Bonatti, B. Yu, *Building Anosov flows on 3-manifolds*, Geom. Topol. 21 (2017) 1837–1930, https://doi.org/10.2140/gt.2017.21.1837 (arXiv:1408.3951v1). Used tacitly in footnote 2 and in the proof of Proposition 1.1 (arXiv v1 Section 3.1); a flow-box argument at the seam. Mission notions: IsPlugGluing, IsPlug, IsBoundaryDiffeo, IsUnionOfComponents, outBoundary, inBoundary; Mathlib notions: IsMIntegralCurveOn, ModelWithCorners.IsInteriorPoint.

import Mathlib
import Definitions.Def_AnosovPlugs_Gluing

open scoped Manifold ContDiff Topology
open Set

namespace AnosovPlugs

theorem plugGluing_localSteps_seam
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
    ∀ x ∈ Tout, I3.IsInteriorPoint (iU x) →
      ∃ ε > (0 : ℝ), ∃ O : Set W, IsOpen O ∧ iU x ∈ O ∧ ∀ h : ℝ, |h| ≤ ε → ∃ f : W → W,
        ContMDiffOn I3 I3 1 f O ∧
        ∀ y ∈ O, ∃ η : ℝ → W, η 0 = y ∧ IsMIntegralCurveOn η Z (uIcc 0 h) ∧ η h = f y := by sorry

end AnosovPlugs
