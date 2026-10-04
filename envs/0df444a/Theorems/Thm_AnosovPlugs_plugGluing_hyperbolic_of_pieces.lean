-- Prove2me | Theorems.Thm_AnosovPlugs_plugGluing_hyperbolic_of_pieces
-- name    : AnosovPlugs.plugGluing_hyperbolic_of_pieces
-- status  : Open
-- author  : @ebayuser
-- created : 2026-10-02T20:30:44.340911+00:00
-- url     : https://prove2.me/theorems/767862ea-3278-4b85-9a8b-b3357467adc7
-- title:
--   Gluing hyperbolic plugs (Béguin–Bonatti–Yu, Prop. 1.1): hyperbolicity extends over the connecting orbits
-- statement:
--   Let $(U,X)$ and $(V,Y)$ be hyperbolic plugs: plugs whose maximal invariant sets $\Lambda_X$, $\Lambda_Y$ are hyperbolic sets with one-dimensional strong stable and strong unstable bundles. Let $T^{out}$ be a union of connected components of $\partial^{out}U$, let $T^{in}$ be a union of connected components of $\partial^{in}V$, and let $\varphi:T^{out}\to T^{in}$ be a C¹ diffeomorphism such that $\varphi_*(L^u_X)$ is transverse to $L^s_Y$: at every point $p\in\varphi(L^u_X\cap T^{out})\cap L^s_Y$, the leaf of $\varphi_*(L^u_X)$ and the leaf of $L^s_Y$ through $p$ are transverse. Here $L^u_X=W^u(\Lambda_X)\cap\partial^{out}U$ is the exit lamination of $(U,X)$ and $L^s_Y=W^s(\Lambda_Y)\cap\partial^{in}V$ is the entrance lamination of $(V,Y)$. Here $W^s(\Lambda_Y)$ is the stable set: the points of $V$ whose forward orbit is defined for all positive times; $W^u(\Lambda_X)$ is the unstable set: the points of $U$ whose backward orbit is defined for all negative times. Let $(W,Z)$ be a gluing of $(U,X)$ and $(V,Y)$ along $\varphi$: C¹ embeddings $i_U:U\to W$ and $i_V:V\to W$ with injective derivatives cover the compact 3-manifold $W$, identify exactly the points $x\in T^{out}$ with $\varphi(x)$, and satisfy $Di_U(X)=Z\circ i_U$, $Di_V(Y)=Z\circ i_V$. Write $\Lambda_Z$ for the maximal invariant set of $Z$. A hyperbolic set of $Z$ with one-dimensional strong stable and strong unstable bundles is a set on which there are a continuous Riemannian metric, line fields $E^s$, $E^u$ with $E^s\oplus\mathbb R Z\oplus E^u=TW$, invariance of $E^s$, $E^u$ under the derivatives of the time-$t$ maps of the flow, and exponential contraction and expansion estimates with constants $C>0$, $\lambda>0$. The *connecting set* $\mathcal C\subseteq W$ is the $Z$-orbit of $\varphi_*(L^u_X)\cap L^s_Y$: the set of points $w$ that lie on a complete integral curve $\gamma:\mathbb R\to W$ of $Z$ with $\gamma(0)=i_U(x)=i_V(\varphi(x))$ for some $x\in L^u_X\cap T^{out}$ with $\varphi(x)\in L^s_Y$. Assume that
--   $$ \Lambda_Z\ =\ i_U(\Lambda_X)\ \cup\ i_V(\Lambda_Y)\ \cup\ \mathcal C, $$
--   and that $i_U(\Lambda_X)$ and $i_V(\Lambda_Y)$ are hyperbolic sets of $Z$ with one-dimensional strong stable and strong unstable bundles. Then
--   $$ \Lambda_Z \text{ is a hyperbolic set of } Z \text{ with one-dimensional strong stable and strong unstable bundles.} $$
--
--   This is the "classical consequence of the hyperbolic theory" invoked in the proof of Proposition 1.1: the hyperbolic structure on $i_U(\Lambda_X)\cup i_V(\Lambda_Y)$ extends over the orbits of $\varphi_*(L^u_X)\cap L^s_Y$, which connect $\Lambda_X$ (in the past) to $\Lambda_Y$ (in the future). The two other hypotheses are the conclusions of the companion statements `plugGluing_maxInvSet_subset`, `plugGluing_maxInvSet_superset` and `plugGluing_pieces_hyperbolic`.
--
--   **Formalization Note** The formal conclusion asserts only that $\Lambda_Z$ is a hyperbolic set in the sense of the mission (`IsHyperbolicSet`, existential in the metric and the bundles). The paper also describes the bundles at a connecting point $x$: the stable bundle is $\mathbb R\,Y(x)\oplus T_xL^s_Y$ and the unstable bundle is $\mathbb R\,(\varphi_*X)(x)\oplus T_x\varphi_*(L^u_X)$ (these are the weak bundles); the formal statement does not assert this description. $Z$ is not assumed to be C¹. Transversality of $\varphi_*(L^u_X)$ and $L^s_Y$ is formalized as in the parent statement, through C¹ curves in the two leaves with linearly independent velocities at $p$ (`CurvesTransverseAt`, `pushLeaf`, `exitLeaf`, `entranceLeaf`). The connecting set is phrased by the existence of a complete integral curve of $Z$ through the gluing point.
-- source:
--   F. Béguin, C. Bonatti, B. Yu, *Building Anosov flows on 3-manifolds*, Geom. Topol. 21 (2017) 1837–1930, https://doi.org/10.2140/gt.2017.21.1837 (arXiv:1408.3951v1), proof of Proposition 1.1, Section 3.1 of arXiv v1 (= Section 4.1 of the published version), p. 14 of arXiv v1. Fifth and last sentence of the proof: 'A classical consequence of the hyperbolic theory asserts that the orbit of φ_*(L^u_X) ∩ L^s_Y inherit of a hyperbolic structure, so that the maximal invariant set of the vector field Z on U ⊔_φ V is hyperbolic: for x ∈ φ_*(L^u_X) ∩ L^s_Y, the stable (resp. unstable) bundle at x is the direct sum of the line R.Y(x) (resp. R.(φ_*X)(x)) and the line tangent to L^s_Y (resp. φ_*(L^u_X)) at x.' Definition 2.2 of arXiv v1.

import Mathlib
import Definitions.Def_AnosovPlugs_Gluing

open scoped Manifold ContDiff Topology
open Set

namespace AnosovPlugs

theorem plugGluing_hyperbolic_of_pieces
    {U : Type} [TopologicalSpace U] [ChartedSpace (EuclideanHalfSpace 3) U]
    [IsManifold I3 ∞ U] [T2Space U] [CompactSpace U]
    {V : Type} [TopologicalSpace V] [ChartedSpace (EuclideanHalfSpace 3) V]
    [IsManifold I3 ∞ V] [T2Space V] [CompactSpace V]
    {W : Type} [TopologicalSpace W] [ChartedSpace (EuclideanHalfSpace 3) W]
    [IsManifold I3 ∞ W] [T2Space W] [CompactSpace W]
    (X : (x : U) → TangentSpace I3 x) (Y : (y : V) → TangentSpace I3 y)
    (hX : IsHyperbolicPlug X) (hY : IsHyperbolicPlug Y)
    (Tout : Set U) (Tin : Set V) (hTout : IsUnionOfComponents Tout (outBoundary X))
    (hTin : IsUnionOfComponents Tin (inBoundary Y)) (φ : U → V)
    (hφ : IsBoundaryDiffeo φ Tout Tin)
    (htransv : ∀ p ∈ φ '' (exitLamination X ∩ Tout) ∩ entranceLamination Y,
      CurvesTransverseAt (pushLeaf φ Tout (exitLeaf X) p) (entranceLeaf Y p) p)
    (Z : (w : W) → TangentSpace I3 w) (iU : U → W) (iV : V → W)
    (hglue : IsPlugGluing X Y Tout φ Z iU iV)
    (hΛ : maxInvSet Z = iU '' maxInvSet X ∪ iV '' maxInvSet Y ∪
      {w | ∃ x ∈ exitLamination X ∩ Tout, φ x ∈ entranceLamination Y ∧
        ∃ γ : ℝ → W, γ 0 = iU x ∧ IsMIntegralCurve γ Z ∧ w ∈ range γ})
    (hU : IsHyperbolicSet Z (iU '' maxInvSet X)) (hV : IsHyperbolicSet Z (iV '' maxInvSet Y)) :
    IsHyperbolicSet Z (maxInvSet Z) := by sorry

end AnosovPlugs
