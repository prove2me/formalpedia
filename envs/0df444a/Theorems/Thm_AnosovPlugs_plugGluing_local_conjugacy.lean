-- Prove2me | Theorems.Thm_AnosovPlugs_plugGluing_local_conjugacy
-- name    : AnosovPlugs.plugGluing_local_conjugacy
-- status  : Proved
-- author  : @ebayuser
-- created : 2026-10-03T01:18:39.153829+00:00
-- url     : https://prove2.me/theorems/8a8c339d-f79d-4787-ac42-6404455eeb04
-- title:
--   Gluing plugs (from the proof of Béguin–Bonatti–Yu, Prop. 1.1): near the maximal invariant sets the glued flow is the flow of the pieces
-- statement:
--   Let $(U,X)$ and $(V,Y)$ be plugs: $X$, $Y$ are nonsingular C¹ vector fields on the compact Hausdorff 3-manifolds with boundary $U$, $V$, transverse to the boundary. Let $T^{out}$ be a union of connected components of $\partial^{out}U$, let $T^{in}$ be a union of connected components of $\partial^{in}V$, and let $\varphi:U\to V$ be any map (no continuity is assumed, and $\varphi$ is not assumed to map $T^{out}$ into $T^{in}$; $T^{in}$ occurs in no other hypothesis). Let $(W,Z)$ be a gluing of $(U,X)$ and $(V,Y)$ along $\varphi$: C¹ embeddings $i_U:U\to W$ and $i_V:V\to W$ with injective derivatives cover the compact Hausdorff 3-manifold $W$, identify exactly the points $x\in T^{out}$ with $\varphi(x)$, and satisfy $Di_U(X)=Z\circ i_U$, $Di_V(Y)=Z\circ i_V$. Write $\Lambda_X$, $\Lambda_Y$ for the maximal invariant sets (points whose orbit is defined for all times) and $X^t$, $Y^t$, $Z^t$ for the time-$t$ maps of the flows. Then:
--
--   1. for every $x\in\Lambda_X$, the image $i_U(U)$ is a neighbourhood of $i_U(x)$ in $W$, and for every real $t$ there is a neighbourhood $O$ of $x$ in $U$ with
--   $$ Z^t(i_U(y)) = i_U(X^t(y))\quad\text{for every } y\in O; $$
--   2. for every $y\in\Lambda_Y$, the image $i_V(V)$ is a neighbourhood of $i_V(y)$ in $W$, and for every real $t$ there is a neighbourhood $O$ of $y$ in $V$ with
--   $$ Z^t(i_V(y')) = i_V(Y^t(y'))\quad\text{for every } y'\in O. $$
--
--   In words: near each point of $\Lambda_X$ (resp. $\Lambda_Y$) the time-$t$ map of $Z$ is the time-$t$ map of $X$ (resp. $Y$) read through the embedding, and the image of the piece is a neighbourhood of the image of that point. This is what the proof of Proposition 1.1 takes for granted when, in its fourth and fifth sentences, it treats $\Lambda_X$ and $\Lambda_Y$ as hyperbolic sets of $Z$ (footnote 2: the differentiable structure of $W$ is compatible with those of $U$ and $V$ by restriction).
--
--   **Formalization Note** The time-$t$ map $X^t$ is the mission's `flowMap`: when some integral curve of $X$ through $x$ is defined on the closed time interval between $0$ and $t$, $X^t(x)$ is the value at time $t$ of a chosen such curve; otherwise $X^t(x)=x$. Nothing in the definition asserts that this choice is unique. The derivative $D(X^t)_x$ is Mathlib's `mfderiv`, which is $0$ where $X^t$ is not differentiable. The identity cannot hold on all of $U$: a point whose $X$-orbit leaves $U$ before time $t$ has $X^t(y)=y$ by convention, while its $Z$-orbit can continue in $W$. So the conjugacy is stated on a neighbourhood of each $x\in\Lambda_X$ (Mathlib's `∀ᶠ y in 𝓝 x`), which is also what the comparison of derivatives needs; its proof needs continuous dependence of the orbits of the C¹ field $X$ on initial conditions (so that orbits of points near $x\in\Lambda_X$ stay in $U$ up to time $t$) together with uniqueness of integral curves of $Z$ inside $i_U(\operatorname{int}U)$ (the lifting lemma `integralCurve_lift_of_embedding` and the uniqueness theorem for C¹ fields at interior points). The neighbourhood statements follow from $\Lambda_X\cap\partial U=\emptyset$, $\Lambda_Y\cap\partial V=\emptyset$ (transversality, `normalCoord_nonneg_of_hasMFDerivWithinAt`) and the inverse function theorem: at an interior point $y$ the derivative $D(i_V)_y$ is a linear isomorphism, so $i_V$ maps a neighbourhood of $y$ onto an open subset of $W$ (and likewise for $i_U$ at points of $\Lambda_X$). The statement carries no hypothesis on $\varphi$ (none is in the parent statement). $Z$ is not assumed to be C¹; it is controlled only through the embeddings.
-- source:
--   F. Béguin, C. Bonatti, B. Yu, *Building Anosov flows on 3-manifolds*, Geom. Topol. 21 (2017) 1837–1930, https://doi.org/10.2140/gt.2017.21.1837 (arXiv:1408.3951v1). Proof of Proposition 1.1, Section 3.1 of arXiv v1 (= Section 4.1 of the published version), p. 14 of arXiv v1, fourth and fifth sentences of the proof ('Then ΛZ is the union of ΛX, ΛY and the Z-orbit of the set φ_*(L^u_X) ∩ L^s_Y'; 'A classical consequence of the hyperbolic theory asserts that [...] the maximal invariant set on the vector field Z on U ⊔_φ V is hyperbolic'), which use without comment that ΛX and ΛY keep their hyperbolic structures in W; and footnote 2 of Section 1 (p. 2): the differentiable structure on W is compatible with those of U and V by restriction. The statement makes explicit the local conjugacy between the flow of Z and the flows of X and Y near Λ_X and Λ_Y that these sentences use. Mission notions: IsPlug, IsPlugGluing, maxInvSet, flowMap.

import Mathlib
import Definitions.Def_AnosovPlugs_Gluing

open scoped Manifold ContDiff Topology
open Set

namespace AnosovPlugs

theorem plugGluing_local_conjugacy
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
    (Z : (w : W) → TangentSpace I3 w) (iU : U → W) (iV : V → W)
    (hglue : IsPlugGluing X Y Tout φ Z iU iV) :
    (∀ x ∈ maxInvSet X, range iU ∈ 𝓝 (iU x) ∧
        ∀ t : ℝ, ∀ᶠ y in 𝓝 x, flowMap Z t (iU y) = iU (flowMap X t y)) ∧
    (∀ y ∈ maxInvSet Y, range iV ∈ 𝓝 (iV y) ∧
        ∀ t : ℝ, ∀ᶠ y' in 𝓝 y, flowMap Z t (iV y') = iV (flowMap Y t y')) := by sorry

end AnosovPlugs
