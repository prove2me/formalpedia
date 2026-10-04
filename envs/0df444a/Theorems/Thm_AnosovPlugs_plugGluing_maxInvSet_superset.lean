-- Prove2me | Theorems.Thm_AnosovPlugs_plugGluing_maxInvSet_superset
-- name    : AnosovPlugs.plugGluing_maxInvSet_superset
-- status  : Proved
-- author  : @ebayuser
-- created : 2026-10-02T20:30:12.73861+00:00
-- url     : https://prove2.me/theorems/11f3bcc9-9f41-4c88-8d2a-6bca5346c5c4
-- title:
--   Gluing plugs (Béguin–Bonatti–Yu, Prop. 1.1): Λ_X, Λ_Y and the connecting orbits lie in the maximal invariant set of the glued field
-- statement:
--   Let $X$ and $Y$ be vector fields on the compact 3-manifolds with boundary $U$ and $V$, let $T^{out}\subseteq U$, and let $\varphi:U\to V$. Write $\partial^{out}U$ for the set of boundary points of $U$ at which $X$ points strictly outward and $\partial^{in}V$ for the set of boundary points of $V$ at which $Y$ points strictly inward. Let $(W,Z)$ be a gluing of $(U,X)$ and $(V,Y)$ along $\varphi$: C¹ embeddings $i_U:U\to W$ and $i_V:V\to W$ with injective derivatives cover the compact 3-manifold $W$, identify exactly the points $x\in T^{out}$ with $\varphi(x)$, and satisfy $Di_U(X)=Z\circ i_U$, $Di_V(Y)=Z\circ i_V$. Write $\Lambda_X$, $\Lambda_Y$, $\Lambda_Z$ for the maximal invariant sets (points whose orbit is defined for all times), $L^u_X$ for the exit lamination of $(U,X)$ (points of $\partial^{out}U$ whose backward orbit is defined for all times) and $L^s_Y$ for the entrance lamination of $(V,Y)$ (points of $\partial^{in}V$ whose forward orbit is defined for all times). The *connecting set* $\mathcal C\subseteq W$ is the $Z$-orbit of $\varphi_*(L^u_X)\cap L^s_Y$: the set of points $w$ that lie on a complete integral curve $\gamma:\mathbb R\to W$ of $Z$ with $\gamma(0)=i_U(x)=i_V(\varphi(x))$ for some $x\in L^u_X\cap T^{out}$ with $\varphi(x)\in L^s_Y$. Then the three pieces lie in the maximal invariant set of $Z$:
--   $$ i_U(\Lambda_X)\ \cup\ i_V(\Lambda_Y)\ \cup\ \mathcal C\ \subseteq\ \Lambda_Z. $$
--
--   This is the inclusion $\supseteq$ in the sentence "$\Lambda_Z$ is the union of $\Lambda_X$, $\Lambda_Y$ and the $Z$-orbit of $\varphi_*(L^u_X)\cap L^s_Y$" of the proof of Proposition 1.1.
--
--   **Formalization Note** No plug or hyperbolicity hypothesis is needed for this inclusion: only the gluing identities. $Z$ is not assumed to be C¹. The connecting set is phrased by the existence of a complete integral curve of $Z$ through the gluing point (see the companion statement `plugGluing_maxInvSet_subset`).
-- source:
--   F. Béguin, C. Bonatti, B. Yu, *Building Anosov flows on 3-manifolds*, Geom. Topol. 21 (2017) 1837–1930, https://doi.org/10.2140/gt.2017.21.1837 (arXiv:1408.3951v1), proof of Proposition 1.1, Section 3.1 of arXiv v1 (= Section 4.1 of the published version), p. 14 of arXiv v1. Fourth sentence of the proof (the sentence that begins 'Then Λ_Z is the union'): 'Then Λ_Z is the union of Λ_X, Λ_Y and the Z-orbit of the set φ_*(L^u_X) ∩ L^s_Y.' This statement is the inclusion ⊇ of that sentence. Definitions 2.1 and Section 2.3 of arXiv v1.

import Mathlib
import Definitions.Def_AnosovPlugs_Gluing

open scoped Manifold ContDiff Topology
open Set

namespace AnosovPlugs

theorem plugGluing_maxInvSet_superset
    {U : Type} [TopologicalSpace U] [ChartedSpace (EuclideanHalfSpace 3) U]
    [IsManifold I3 ∞ U] [T2Space U] [CompactSpace U]
    {V : Type} [TopologicalSpace V] [ChartedSpace (EuclideanHalfSpace 3) V]
    [IsManifold I3 ∞ V] [T2Space V] [CompactSpace V]
    {W : Type} [TopologicalSpace W] [ChartedSpace (EuclideanHalfSpace 3) W]
    [IsManifold I3 ∞ W] [T2Space W] [CompactSpace W]
    (X : (x : U) → TangentSpace I3 x) (Y : (y : V) → TangentSpace I3 y)
    (Tout : Set U) (φ : U → V)
    (Z : (w : W) → TangentSpace I3 w) (iU : U → W) (iV : V → W)
    (hglue : IsPlugGluing X Y Tout φ Z iU iV) :
    iU '' maxInvSet X ∪ iV '' maxInvSet Y ∪
      {w | ∃ x ∈ exitLamination X ∩ Tout, φ x ∈ entranceLamination Y ∧
        ∃ γ : ℝ → W, γ 0 = iU x ∧ IsMIntegralCurve γ Z ∧ w ∈ range γ} ⊆ maxInvSet Z := by sorry

end AnosovPlugs
