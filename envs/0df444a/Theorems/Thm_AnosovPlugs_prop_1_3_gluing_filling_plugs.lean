-- Prove2me | Theorems.Thm_AnosovPlugs_prop_1_3_gluing_filling_plugs
-- name    : AnosovPlugs.prop_1_3_gluing_filling_plugs
-- status  : Open
-- author  : @Lucas
-- created : 2026-10-01T02:47:45.650469+00:00
-- url     : https://prove2.me/theorems/fbe93104-741d-4938-bb88-2db57f4c10de
-- title:
--   Proposition 1.3 (Béguin–Bonatti–Yu): strongly transverse gluing preserves filling MS laminations
-- statement:
--   In the setting of Proposition 1.1, assume furthermore that the plugs $(U,X)$ and $(V,Y)$ have filling MS laminations and that $\varphi_*(L^u_X)$ is strongly transverse to $L^s_Y$. Then
--   $$ (W,Z) \text{ has filling MS laminations.}$$
--
--   **Formalization Note** As in Proposition 1.1, $W$ is any compact smooth manifold realising the gluing. The conclusion states that $Z$ is nonsingular and transverse to $\partial W$, that its maximal invariant set is hyperbolic, and that every complementary component of its entrance and exit laminations is a strip.
-- source:
--   F. Béguin, C. Bonatti, B. Yu, *Building Anosov flows on 3-manifolds*, Geom. Topol. 21 (2017) 1837–1930, https://doi.org/10.2140/gt.2017.21.1837, p. 1841, Proposition 1.3 (proof in §4.2)

import Mathlib
import Definitions.Def_AnosovPlugs_Gluing

open scoped Manifold ContDiff Topology
open Set

namespace AnosovPlugs

theorem prop_1_3_gluing_filling_plugs
    {U : Type} [TopologicalSpace U] [ChartedSpace (EuclideanHalfSpace 3) U]
    [IsManifold I3 ∞ U] [T2Space U] [CompactSpace U]
    {V : Type} [TopologicalSpace V] [ChartedSpace (EuclideanHalfSpace 3) V]
    [IsManifold I3 ∞ V] [T2Space V] [CompactSpace V]
    {W : Type} [TopologicalSpace W] [ChartedSpace (EuclideanHalfSpace 3) W]
    [IsManifold I3 ∞ W] [T2Space W] [CompactSpace W]
    (X : (x : U) → TangentSpace I3 x) (Y : (y : V) → TangentSpace I3 y)
    (hX : IsFillingHyperbolicPlug X) (hY : IsFillingHyperbolicPlug Y)
    (Tout : Set U) (Tin : Set V) (hTout : IsUnionOfComponents Tout (outBoundary X))
    (hTin : IsUnionOfComponents Tin (inBoundary Y)) (φ : U → V)
    (hφ : IsBoundaryDiffeo φ Tout Tin)
    (hstrong : StronglyTransverse Tin (φ '' (exitLamination X ∩ Tout))
      (entranceLamination Y ∩ Tin) (pushLeaf φ Tout (exitLeaf X)) (entranceLeaf Y))
    (Z : (w : W) → TangentSpace I3 w) (iU : U → W) (iV : V → W)
    (hglue : IsPlugGluing X Y Tout φ Z iU iV) :
    IsNonsingularTransverse Z ∧ IsHyperbolicSet Z (maxInvSet Z) ∧
      HasFillingLaminations Z := by sorry

end AnosovPlugs
