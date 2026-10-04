-- Prove2me | Theorems.Thm_AnosovPlugs_plugGluing_pieces_hyperbolic
-- name    : AnosovPlugs.plugGluing_pieces_hyperbolic
-- status  : Proved
-- author  : @ebayuser
-- created : 2026-10-02T20:30:27.330098+00:00
-- url     : https://prove2.me/theorems/31f9b7f6-3149-4ee7-b585-e8aab1101366
-- title:
--   Gluing hyperbolic plugs (Béguin–Bonatti–Yu, Prop. 1.1): the images of Λ_X and Λ_Y are hyperbolic sets of the glued field
-- statement:
--   Let $(U,X)$ and $(V,Y)$ be hyperbolic plugs: plugs whose maximal invariant sets $\Lambda_X$, $\Lambda_Y$ are hyperbolic sets with one-dimensional strong stable and strong unstable bundles. Let $T^{out}$ be a union of connected components of $\partial^{out}U$, let $T^{in}$ be a union of connected components of $\partial^{in}V$, and let $\varphi:U\to V$. Let $(W,Z)$ be a gluing of $(U,X)$ and $(V,Y)$ along $\varphi$: C¹ embeddings $i_U:U\to W$ and $i_V:V\to W$ with injective derivatives cover the compact 3-manifold $W$, identify exactly the points $x\in T^{out}$ with $\varphi(x)$, and satisfy $Di_U(X)=Z\circ i_U$, $Di_V(Y)=Z\circ i_V$. Then the images of the two maximal invariant sets are hyperbolic sets of $Z$:
--   $$ i_U(\Lambda_X)\ \text{and}\ i_V(\Lambda_Y)\ \text{are hyperbolic sets of } Z \text{ with one-dimensional strong stable and strong unstable bundles.} $$
--
--   This is the part of the proof of Proposition 1.1 where the hyperbolic structures of $\Lambda_X$ and $\Lambda_Y$ are regarded as hyperbolic structures for $Z$ on $W$.
--
--   **Formalization Note** A hyperbolic set is defined as in the mission (`IsHyperbolicSet`): a continuous Riemannian metric, line fields $E^s$, $E^u$ with $E^s\oplus\mathbb R Z\oplus E^u=TW$ on the set, invariance under the derivatives of the time-$t$ maps of the flow, and exponential estimates with constants $C>0$, $\lambda>0$. $Z$ is not assumed to be C¹. The hypotheses on $T^{out}$ and $T^{in}$ are those of Proposition 1.1; the map $\varphi$ enters only through the gluing relation.
-- source:
--   F. Béguin, C. Bonatti, B. Yu, *Building Anosov flows on 3-manifolds*, Geom. Topol. 21 (2017) 1837–1930, https://doi.org/10.2140/gt.2017.21.1837 (arXiv:1408.3951v1), proof of Proposition 1.1, Section 3.1 of arXiv v1 (= Section 4.1 of the published version), p. 14 of arXiv v1. Implicit in the last sentence of the proof ('so that the maximal invariant set of the vector field Z on U ⊔_φ V is hyperbolic'): the hyperbolic structures of Λ_X and Λ_Y are carried to W by the embeddings. Definition 2.2 of arXiv v1 (hyperbolic plug, hyperbolic set with one-dimensional strong bundles).

import Mathlib
import Definitions.Def_AnosovPlugs_Gluing

open scoped Manifold ContDiff Topology
open Set

namespace AnosovPlugs

theorem plugGluing_pieces_hyperbolic
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
    (Z : (w : W) → TangentSpace I3 w) (iU : U → W) (iV : V → W)
    (hglue : IsPlugGluing X Y Tout φ Z iU iV) :
    IsHyperbolicSet Z (iU '' maxInvSet X) ∧ IsHyperbolicSet Z (iV '' maxInvSet Y) := by sorry

end AnosovPlugs
