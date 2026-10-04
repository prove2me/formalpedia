-- Prove2me | Theorems.Thm_AnosovPlugs_plugGluing_integralCurveOn_unique
-- name    : AnosovPlugs.plugGluing_integralCurveOn_unique
-- status  : Proved
-- author  : @ebayuser
-- created : 2026-10-03T20:57:43.901986+00:00
-- url     : https://prove2.me/theorems/9fe834dd-3321-4321-bf4b-d9b1f4f28a1b
-- title:
--   Integral curves of the glued vector field of a plug gluing are unique, also through the seam
-- statement:
--   Let $(U,X)$ and $(V,Y)$ be plugs: compact Hausdorff smooth 3-manifolds with boundary carrying nonsingular C¹ vector fields transverse to the boundary. Let $T^{out}\subseteq\partial^{out}U$ and $T^{in}\subseteq\partial^{in}V$ be unions of connected components of the exit and entrance boundaries, and let $\varphi:T^{out}\to T^{in}$ be a C¹ diffeomorphism (the mission's `IsBoundaryDiffeo`). Let $(W,Z,i_U,i_V)$ be a plug gluing (the mission's `IsPlugGluing`): $W$ is a compact Hausdorff smooth 3-manifold with boundary, $i_U:U\to W$ and $i_V:V\to W$ are C¹ embeddings with injective derivatives whose images cover $W$ and meet exactly along the seam $i_U(x)=i_V(\varphi(x))$, $x\in T^{out}$, and $Z$ is the vector field on $W$ with $Z\circ i_U=Di_U\circ X$ and $Z\circ i_V=Di_V\circ Y$. The field $Z$ is not assumed to be C¹. An *integral curve of a vector field $F$ on a manifold $N$ on a set of times* $S\subseteq\mathbb R$ is a curve $\gamma:\mathbb R\to N$ whose derivative within $S$ at every $u\in S$ is $F(\gamma(u))$ (Mathlib's `IsMIntegralCurveOn`; at the endpoints of an interval the derivative is one-sided). We write $[0,t]$ for the closed interval between $0$ and $t$, in either order (Mathlib's `uIcc 0 t`). Then integral curves of the glued field $Z$ are determined by their starting point: for every $t\in\mathbb R$ and all integral curves $\gamma,\gamma'$ of $Z$ on $[0,t]$ with $\gamma'(0)=\gamma(0)$,
--   $$ \gamma'(s)=\gamma(s)\quad\text{for all } s\in[0,t]. $$
--
--   In words: although $Z$ is not known to be C¹ on $W$, its integral curves are unique, also through the seam. The proof shows first that $i_V(V)$ is forward invariant and $i_U(U)$ is backward invariant for every integral curve of $Z$. Suppose that an integral curve leaves $i_V(V)$. Its lift to $U$ then starts at a point of $T^{out}\subseteq\partial^{out}U$, where $X$ points outward. The one-sided derivative at a boundary point forbids this. The mirror argument uses $T^{in}\subseteq\partial^{in}V$. So from any time of agreement, both curves stay for a while in one piece, where they lift to integral curves of $X$ or $Y$ (`integralCurve_lift_of_embedding`) with the same starting point, and uniqueness on a manifold with boundary (`integralCurveOn_uIcc_unique`) applies; the set of agreement times is then closed and open in $[0,t]$. It is used in the proof of Proposition 1.1 (Section 3.1 of arXiv v1, p. 14; GT 2017 Section 4.1). There it makes the time-$t$ maps of $Z$ along the connecting orbits the maps given by those orbits, and it makes the two pieces of the maximal invariant set invariant under the flow of $Z$.
--
--   **Formalization Note** The hypotheses are those of the mission's gluing statements. Of the plug hypotheses only the C¹ regularity of $X$ and $Y$ is used (through `integralCurveOn_uIcc_unique`); Compactness of $U$ and $V$ and the Hausdorff property of $W$ make the images $i_U(U)$ and $i_V(V)$ closed. The Hausdorff property of $U$ and $V$ is used by `integralCurveOn_uIcc_unique`; it also follows from the embeddings into $W$. Of `hTout` and `hTin` only $T^{out}\subseteq\partial^{out}U$ (forward direction) and $T^{in}\subseteq\partial^{in}V$ (backward direction) are used. $\varphi$ enters only through $\varphi(T^{out})\subseteq T^{in}$. Compactness of $W$ and the hyperbolicity of the plugs are not used.
-- source:
--   F. Béguin, C. Bonatti, B. Yu, *Building Anosov flows on 3-manifolds*, Geom. Topol. 21 (2017) 1837–1930, https://doi.org/10.2140/gt.2017.21.1837 (arXiv:1408.3951v1). General fact about plug gluings, used tacitly in footnote 2 and in the proof of Proposition 1.1 (arXiv v1 Section 3.1, GT 2017 Section 4.1). Mission notions: IsPlugGluing, IsBoundaryDiffeo, IsUnionOfComponents, outBoundary, inBoundary; companion theorems integralCurveOn_uIcc_unique, integralCurve_lift_of_embedding, normalCoord_nonneg_of_hasMFDerivWithinAt.

import Mathlib
import Definitions.Def_AnosovPlugs_Gluing

open scoped Manifold ContDiff Topology
open Set

namespace AnosovPlugs

theorem plugGluing_integralCurveOn_unique
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
    ∀ (γ γ' : ℝ → W) (t : ℝ), IsMIntegralCurveOn γ Z (uIcc 0 t) → IsMIntegralCurveOn γ' Z (uIcc 0 t) →
      γ' 0 = γ 0 → ∀ s ∈ uIcc 0 t, γ' s = γ s := by sorry

end AnosovPlugs
