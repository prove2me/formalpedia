-- Prove2me | Theorems.Thm_AnosovPlugs_plugGluing_maxInvSet_hyperbolic
-- name    : AnosovPlugs.plugGluing_maxInvSet_hyperbolic
-- status  : Open
-- author  : @ebayuser
-- created : 2026-10-02T17:14:37.677293+00:00
-- url     : https://prove2.me/theorems/83e416c9-2684-4696-abcf-0df7888786ed
-- title:
--   Gluing plugs (Béguin–Bonatti–Yu, Prop. 1.1): the maximal invariant set of the glued plug is hyperbolic
-- statement:
--   Let $(U,X)$ and $(V,Y)$ be hyperbolic plugs, let $T^{out}$ be a union of connected components of $\partial^{out}U$ and $T^{in}$ a union of connected components of $\partial^{in}V$, let $\varphi:T^{out}\to T^{in}$ be a diffeomorphism, and let $(W,Z)$ be the glued manifold $(U\sqcup V)/\varphi$ with the vector field induced by $X$ and $Y$: C¹ embeddings $i_U:U\to W$, $i_V:V\to W$ cover $W$, identify exactly the points $x\in T^{out}$ with $\varphi(x)$, and push $X$ and $Y$ to $Z$.
--
--   Assume that $\varphi_*(L^u_X)$ is transverse to the lamination $L^s_Y$ at every point of $\varphi(L^u_X\cap T^{out})\cap L^s_Y$. Then the maximal invariant set $\Lambda_Z$ of $(W,Z)$ is a hyperbolic set with one-dimensional strong stable and strong unstable bundles:
--   $$ \Lambda_Z=\Lambda_X\cup\Lambda_Y\cup\bigcup_{t\in\mathbb R}Z^t\big(\varphi_*(L^u_X)\cap L^s_Y\big)\ \text{ is hyperbolic.} $$
--
--   This is the core of Proposition 1.1. The new orbits of $\Lambda_Z$ are the heteroclinic orbits through the transverse intersection $\varphi_*(L^u_X)\cap L^s_Y$; at such a point the stable bundle is spanned by $Y$ and the tangent line of $L^s_Y$, the unstable bundle by $\varphi_*X$ and the tangent line of $\varphi_*(L^u_X)$, and the classical theory of hyperbolic sets without cycles gives uniform contraction and expansion along the whole orbit.
--
--   **Formalization Note** The hypotheses are exactly those of the mission's Proposition 1.1 (`prop_1_1_gluing_hyperbolic_plugs`); the conclusion is its second conjunct, `IsHyperbolicSet Z (maxInvSet Z)`, with the mission's definition of a hyperbolic set (a continuous Riemannian metric, invariant line fields and constants $C,\lambda>0$).
-- source:
--   F. Béguin, C. Bonatti, B. Yu, *Building Anosov flows on 3-manifolds*, Geom. Topol. 21 (2017) 1837–1930, https://doi.org/10.2140/gt.2017.21.1837 (arXiv:1408.3951v1), proof of Proposition 1.1, Section 3.1 of arXiv v1 (= Section 4.1 of the published version), p. 14 of arXiv v1. Second paragraph of the proof: Λ_Z is the union of Λ_X, Λ_Y and the Z-orbit of φ_*(L^u_X) ∩ L^s_Y, and 'a classical consequence of the hyperbolic theory' gives the hyperbolic structure on the orbit of this transverse intersection.

import Mathlib
import Definitions.Def_AnosovPlugs_Gluing

open scoped Manifold ContDiff Topology
open Set

namespace AnosovPlugs

theorem plugGluing_maxInvSet_hyperbolic
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
    (hglue : IsPlugGluing X Y Tout φ Z iU iV) :
    IsHyperbolicSet Z (maxInvSet Z) := by sorry

end AnosovPlugs
