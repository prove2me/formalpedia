-- Prove2me | Theorems.Thm_AnosovPlugs_plugGluing_maxInvSet_subset
-- name    : AnosovPlugs.plugGluing_maxInvSet_subset
-- status  : Proved
-- author  : @ebayuser
-- created : 2026-10-02T20:29:51.861556+00:00
-- url     : https://prove2.me/theorems/77749705-4e2c-4a3f-9feb-50b7f52f987c
-- title:
--   Gluing plugs (Béguin–Bonatti–Yu, Prop. 1.1): the maximal invariant set of the glued field is contained in Λ_X ∪ Λ_Y ∪ (connecting orbits)
-- statement:
--   Let $(U,X)$ and $(V,Y)$ be plugs: $X$, $Y$ are nonsingular C¹ vector fields on the compact 3-manifolds with boundary $U$, $V$, transverse to the boundary. Let $T^{out}$ be a union of connected components of the exit boundary $\partial^{out}U$, let $T^{in}$ be a union of connected components of the entrance boundary $\partial^{in}V$, and let $\varphi:T^{out}\to T^{in}$ be a C¹ diffeomorphism. Let $(W,Z)$ be a gluing of $(U,X)$ and $(V,Y)$ along $\varphi$: C¹ embeddings $i_U:U\to W$ and $i_V:V\to W$ with injective derivatives cover the compact 3-manifold $W$, identify exactly the points $x\in T^{out}$ with $\varphi(x)$, and satisfy $Di_U(X)=Z\circ i_U$, $Di_V(Y)=Z\circ i_V$. Write $\Lambda_X$, $\Lambda_Y$, $\Lambda_Z$ for the maximal invariant sets (points whose orbit is defined for all times), $L^u_X=W^u(\Lambda_X)\cap\partial^{out}U$ for the exit lamination of $(U,X)$ and $L^s_Y=W^s(\Lambda_Y)\cap\partial^{in}V$ for the entrance lamination of $(V,Y)$. Here $W^s(\Lambda_Y)$ is the stable set: the points of $V$ whose forward orbit is defined for all positive times; $W^u(\Lambda_X)$ is the unstable set: the points of $U$ whose backward orbit is defined for all negative times. The *connecting set* $\mathcal C\subseteq W$ is the $Z$-orbit of $\varphi_*(L^u_X)\cap L^s_Y$: the set of points $w$ that lie on a complete integral curve $\gamma:\mathbb R\to W$ of $Z$ with $\gamma(0)=i_U(x)=i_V(\varphi(x))$ for some $x\in L^u_X\cap T^{out}$ with $\varphi(x)\in L^s_Y$. Then every point of the maximal invariant set of $Z$ lies in one of the three pieces:
--   $$ \Lambda_Z\ \subseteq\ i_U(\Lambda_X)\ \cup\ i_V(\Lambda_Y)\ \cup\ \mathcal C. $$
--
--   This is the inclusion $\subseteq$ in the sentence "$\Lambda_Z$ is the union of $\Lambda_X$, $\Lambda_Y$ and the $Z$-orbit of $\varphi_*(L^u_X)\cap L^s_Y$" of the proof of Proposition 1.1.
--
--   **Formalization Note** Only the plug hypotheses on $X$ and $Y$ are assumed (not hyperbolicity). $Z$ is not assumed to be C¹; it is controlled only through the embeddings. The connecting set is phrased by the existence of a complete integral curve of $Z$ through the gluing point, not through a flow map, because uniqueness of integral curves of $Z$ is not among the hypotheses. The hypotheses on $\varphi$, $T^{out}$ and $T^{in}$ are those of Proposition 1.1. The maximal invariant set, the stable set and the unstable set are defined by integral curves in the sense of Mathlib's `IsMIntegralCurve` / `IsMIntegralCurveOn` (one-sided derivatives at interval endpoints).
-- source:
--   F. Béguin, C. Bonatti, B. Yu, *Building Anosov flows on 3-manifolds*, Geom. Topol. 21 (2017) 1837–1930, https://doi.org/10.2140/gt.2017.21.1837 (arXiv:1408.3951v1), proof of Proposition 1.1, Section 3.1 of arXiv v1 (= Section 4.1 of the published version), p. 14 of arXiv v1. Fourth sentence of the proof (the sentence that begins 'Then Λ_Z is the union'): 'Then Λ_Z is the union of Λ_X, Λ_Y and the Z-orbit of the set φ_*(L^u_X) ∩ L^s_Y.' This statement is the inclusion ⊆ of that sentence. Definitions 2.1 (plug, maximal invariant set, stable and unstable sets) and Section 2.3 (laminations L^s, L^u) of arXiv v1.

import Mathlib
import Definitions.Def_AnosovPlugs_Gluing

open scoped Manifold ContDiff Topology
open Set

namespace AnosovPlugs

theorem plugGluing_maxInvSet_subset
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
    maxInvSet Z ⊆ iU '' maxInvSet X ∪ iV '' maxInvSet Y ∪
      {w | ∃ x ∈ exitLamination X ∩ Tout, φ x ∈ entranceLamination Y ∧
        ∃ γ : ℝ → W, γ 0 = iU x ∧ IsMIntegralCurve γ Z ∧ w ∈ range γ} := by sorry

end AnosovPlugs
