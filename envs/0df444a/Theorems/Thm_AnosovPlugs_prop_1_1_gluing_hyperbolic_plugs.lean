-- Prove2me | Theorems.Thm_AnosovPlugs_prop_1_1_gluing_hyperbolic_plugs
-- name    : AnosovPlugs.prop_1_1_gluing_hyperbolic_plugs
-- status  : Open
-- author  : @Lucas
-- created : 2026-10-01T02:33:15.490572+00:00
-- url     : https://prove2.me/theorems/1f28b73e-51cd-4983-be66-b5eb9f6f01f2
-- title:
--   Proposition 1.1 (Béguin–Bonatti–Yu): gluing two hyperbolic plugs gives a hyperbolic plug
-- statement:
--   Let $(U,X)$ and $(V,Y)$ be hyperbolic plugs. Let $T^{out}$ be a union of connected components of $\partial^{out}U$ and $T^{in}$ a union of connected components of $\partial^{in}V$, and let $\varphi:T^{out}\to T^{in}$ be a diffeomorphism such that $\varphi_*(L^u_X)$ is transverse to the lamination $L^s_Y$. Let $Z$ be the vector field induced by $X$ and $Y$ on $W:=(U\sqcup V)/\varphi$. Then
--   $$ (W,Z) \text{ is a hyperbolic plug.}$$
--
--   This is the elementary gluing operation of the "construction game" of the paper.
--
--   **Formalization Note** $W$ is any compact smooth 3-manifold with C¹ embeddings $i_U,i_V$ realising the gluing and pushing $X,Y$ to $Z$. The conclusion is that $Z$ is nonsingular, transverse to $\partial W$, and has hyperbolic maximal invariant set; C¹ regularity of $Z$ is not asserted.
-- source:
--   F. Béguin, C. Bonatti, B. Yu, *Building Anosov flows on 3-manifolds*, Geom. Topol. 21 (2017) 1837–1930, https://doi.org/10.2140/gt.2017.21.1837, p. 1839, Proposition 1.1 (proof in §4.1)

import Mathlib
import Definitions.Def_AnosovPlugs_Gluing

open scoped Manifold ContDiff Topology
open Set

namespace AnosovPlugs

theorem prop_1_1_gluing_hyperbolic_plugs
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
    IsNonsingularTransverse Z ∧ IsHyperbolicSet Z (maxInvSet Z) := by sorry

end AnosovPlugs
