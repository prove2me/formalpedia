-- Prove2me | Theorems.Thm_AnosovPlugs_plugGluing_transverse_boundary
-- name    : AnosovPlugs.plugGluing_transverse_boundary
-- status  : Proved
-- author  : @ebayuser
-- created : 2026-10-02T17:14:34.177745+00:00
-- url     : https://prove2.me/theorems/fbf60454-b2ef-43a7-ba1e-b8c8578482f9
-- title:
--   Gluing plugs (Béguin–Bonatti–Yu, Prop. 1.1): the induced vector field is transverse to the boundary
-- statement:
--   Let $(U,X)$ and $(V,Y)$ be hyperbolic plugs, let $T^{out}$ be a union of connected components of $\partial^{out}U$ and $T^{in}$ a union of connected components of $\partial^{in}V$, let $\varphi:T^{out}\to T^{in}$ be a diffeomorphism, and let $(W,Z)$ be the glued manifold $(U\sqcup V)/\varphi$ with the vector field induced by $X$ and $Y$: C¹ embeddings $i_U:U\to W$, $i_V:V\to W$ cover $W$, identify exactly the points $x\in T^{out}$ with $\varphi(x)$, and push $X$ and $Y$ to $Z$.
--
--   Assume only that $(U,X)$ and $(V,Y)$ are plugs ($X$, $Y$ nonsingular, C¹, transverse to the boundary). Then the induced field $Z$ is transverse to the boundary of $W$:
--   $$ Z(w)\notin T_w\,\partial W\quad\text{for every } w\in\partial W. $$
--
--   This is the second half of the claim "$(W,Z)$ is a plug" in the proof of Proposition 1.1. The boundary of $W$ is the image of the non-glued boundary components $(\partial U\setminus T^{out})\sqcup(\partial V\setminus T^{in})$, and a C¹ embedding of a manifold with boundary onto a neighbourhood of a boundary point maps the inward normal direction to the inward normal direction, so transversality of $X$ and $Y$ to $\partial U$ and $\partial V$ passes to $Z$.
--
--   **Formalization Note** Transversality at a boundary point $w$ is $v_0\neq0$ for the vector $Z(w)$ written in the half-space chart at $w$ (`normalCoord`), the mission's convention. The statement needs invariance of the boundary under C¹ embeddings of 3-manifolds with boundary, which Mathlib does not yet provide; this is the reusable content of the lemma.
-- source:
--   F. Béguin, C. Bonatti, B. Yu, *Building Anosov flows on 3-manifolds*, Geom. Topol. 21 (2017) 1837–1930, https://doi.org/10.2140/gt.2017.21.1837 (arXiv:1408.3951v1), proof of Proposition 1.1, Section 3.1 of arXiv v1 (= Section 4.1 of the published version), p. 14 of arXiv v1. First sentence of the proof: 'The vector field Z is transverse to the boundary of W; hence (W,Z) is a plug.' Compare Proposition 3.1 (= GT 4.1) for the description of the exit boundary of W.

import Mathlib
import Definitions.Def_AnosovPlugs_Gluing

open scoped Manifold ContDiff Topology
open Set

namespace AnosovPlugs

theorem plugGluing_transverse_boundary
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
    ∀ w ∈ I3.boundary W, normalCoord (Z w) ≠ 0 := by sorry

end AnosovPlugs
