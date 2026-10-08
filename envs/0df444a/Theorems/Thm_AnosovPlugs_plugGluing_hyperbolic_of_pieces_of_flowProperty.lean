-- Prove2me | Theorems.Thm_AnosovPlugs_plugGluing_hyperbolic_of_pieces_of_flowProperty
-- name    : AnosovPlugs.plugGluing_hyperbolic_of_pieces_of_flowProperty
-- status  : Open
-- author  : @ebayuser
-- created : 2026-10-04T23:58:22.66831+00:00
-- url     : https://prove2.me/theorems/866b2fce-3fcb-47e3-bf35-f16d71485891
-- title:
--   Hyperbolicity of the maximal invariant set of a transverse plug gluing, given one metric, uniqueness, C¹ time-t maps and the flow properties
-- statement:
--   Let $(U,X)$ and $(V,Y)$ be plugs: compact Hausdorff smooth 3-manifolds with boundary carrying nonsingular C¹ vector fields transverse to the boundary. Let $T^{out}\subseteq\partial^{out}U$ and $T^{in}\subseteq\partial^{in}V$ be unions of connected components of the exit and entrance boundaries, and let $\varphi:T^{out}\to T^{in}$ be a C¹ diffeomorphism (the mission's `IsBoundaryDiffeo`). Let $(W,Z,i_U,i_V)$ be a plug gluing (the mission's `IsPlugGluing`): $W$ is a compact Hausdorff smooth 3-manifold with boundary, $i_U:U\to W$ and $i_V:V\to W$ are C¹ embeddings with injective derivatives whose images cover $W$ and meet exactly along the seam $i_U(x)=i_V(\varphi(x))$, $x\in T^{out}$, and $Z$ is the vector field on $W$ with $Z\circ i_U=Di_U\circ X$ and $Z\circ i_V=Di_V\circ Y$. The field $Z$ is not assumed to be C¹. Assume in addition that $(U,X)$ and $(V,Y)$ are hyperbolic plugs (their maximal invariant sets $\Lambda_X$, $\Lambda_Y$ are hyperbolic sets), and that the gluing is transverse: at every point $p\in\varphi(L^u_X\cap T^{out})\cap L^s_Y$ the pushed exit leaf $\varphi_*(\text{leaf of } L^u_X)$ and the entrance leaf of $L^s_Y$ through $p$ are transverse curves in $\partial V$ (the mission's `CurvesTransverseAt`), where $L^u_X$ and $L^s_Y$ are the exit and entrance laminations. A set $\Lambda\subseteq M$ of a 3-manifold $M$ is a *hyperbolic set* of a vector field $F$ on $M$ (the mission's `IsHyperbolicSet F Λ`) if there are a continuous Riemannian metric $g$, line fields $E^s$, $E^u$ on $\Lambda$ and constants $C>0$, $\lambda>0$ such that at every $x\in\Lambda$: $E^s_x\oplus\mathbb R F(x)\oplus E^u_x=T_xM$, the two line fields are invariant under the derivatives of the time-$t$ maps $\phi_t$ of the flow of $F$ for all $t\in\mathbb R$, and $\|D\phi_t(v)\|_g\le C e^{-\lambda t}\|v\|_g$ for $v\in E^s_x$, $t\ge0$, and $\|D\phi_{-t}(v)\|_g\le C e^{-\lambda t}\|v\|_g$ for $v\in E^u_x$, $t\ge0$. The time-$t$ map is the mission's `flowMap F t`, which sends $x$ to $\gamma(t)$ for a chosen integral curve $\gamma$ of $F$ on $[0,t]$ with $\gamma(0)=x$ when one exists, and to $x$ otherwise. We write $\phi^Z_t$ for the time-$t$ map of $Z$, the mission's `flowMap Z t`: it sends $y$ to $\gamma(t)$ for a chosen integral curve $\gamma$ of $Z$ on $[0,t]$ with $\gamma(0)=y$ when one exists (the mission's `FlowDefined Z y t`), and to $y$ otherwise. Assume the maximal invariant set of $Z$ is described (the hypothesis `hΛ`, proved in the mission as `plugGluing_maxInvSet_subset` and `plugGluing_maxInvSet_superset`):
--   $$ \Lambda_Z = i_U(\Lambda_X)\ \cup\ i_V(\Lambda_Y)\ \cup\ \{\text{points of complete } Z\text{-orbits through } i_U(x),\ x\in L^u_X\cap T^{out},\ \varphi(x)\in L^s_Y\}. $$
--   Assume further the following. Each is the conclusion of another mission theorem, applied to the data above:
--   1. (one metric for both pieces) a continuous Riemannian metric $g$ on $W$ together with line fields and constants, separately for each piece, that make $i_U(\Lambda_X)$ and $i_V(\Lambda_Y)$ hyperbolic sets of $Z$ with respect to this same $g$ (`isHyperbolicSet_of_metric` applied to `plugGluing_pieces_hyperbolic`);
--   2. (uniqueness) integral curves of $Z$ on $[0,t]$ are determined by their starting point, for every $t$ (`plugGluing_integralCurveOn_unique`);
--   3. (C¹ time-$t$ maps) for every point $w$ of the maximal invariant set $\Lambda_Z$ (the points that lie on an integral curve of $Z$ defined for all times), $w$ is an interior point of $W$, and for every $t\in\mathbb R$ there is an open neighbourhood $O$ of $w$ such that the orbit of every $y\in O$ is defined on $[0,t]$ and $\phi^Z_t$ is of class C¹ on $O$ (`plugGluing_flowMap_contMDiffOn`);
--   4. (flow properties) for every $w\in\Lambda_Z$: $\phi^Z_t(w)\in\Lambda_Z$; $\phi^Z_t(\phi^Z_s(w))=\phi^Z_{s+t}(w)$; $D\phi^Z_0(w)=\mathrm{id}$; $D\phi^Z_{s+t}(w)=D\phi^Z_t(\phi^Z_s(w))\circ D\phi^Z_s(w)$; $D\phi^Z_t(w)Z(w)=Z(\phi^Z_t(w))$ (`flowMap_flowProperty_of_regularity`);
--   5. (invariant pieces) $\phi^Z_t(i_U(\Lambda_X))\subseteq i_U(\Lambda_X)$ and $\phi^Z_t(i_V(\Lambda_Y))\subseteq i_V(\Lambda_Y)$ for all $t$ (`plugGluing_pieces_flowMap_invariant`).
--
--   Then the whole maximal invariant set is hyperbolic:
--   $$ \Lambda_Z \text{ is a hyperbolic set of } Z. $$
--
--   In words: this is the fifth sentence of the paper's proof of Proposition 1.1, which says that, by a classical consequence of the hyperbolic theory, the orbit of $\varphi_*(L^u_X)\cap L^s_Y$ inherits a hyperbolic structure, with the paper's description of the bundles at a connecting point $y\in T^{in}$: the stable bundle is $\mathbb R\,Y(y)\oplus T_yL^s_Y$ and the unstable bundle is $\mathbb R\,\varphi_*X(y)\oplus T_y\varphi_*(L^u_X)$, pushed into $W$ by $Di_V$.
--
--   **Formalization Note** This theorem is `plugGluing_hyperbolic_of_pieces_of_regularity` with two added hypotheses, each the verbatim conclusion of a mission theorem (hypotheses 4 and 5). The flow properties of `flowMap Z` and the invariance of the pieces are now hypotheses. The transport of the derivative of `flowMap Z` through the seam, by the derivatives of $i_U$, $\varphi$ and $i_V$, is still inside this theorem. Two classical theorems remain to be proved inside this theorem, and Mathlib (at the pinned version) has neither. The first is the stable manifold theorem for the hyperbolic sets $\Lambda_X$ and $\Lambda_Y$: the points whose forward orbit stays in $V$ carry a contracted line field, and a C¹ curve inside a leaf of $L^s_Y$ is tangent to the sum of this line and the direction of the field; without it, the transversality hypothesis on the leaves gives no information on the bundles. The second is the extension of hyperbolicity over transverse heteroclinic orbits (cone fields near the two pieces, their transport along the connecting orbits, uniform constants). The paper's description of the bundles at connecting points is not asserted, because `IsHyperbolicSet` is existential in the bundles. The field $Z$ is not assumed C¹; the time-$t$ map `flowMap Z t` is junk-valued where no integral curve exists.
-- source:
--   F. Béguin, C. Bonatti, B. Yu, *Building Anosov flows on 3-manifolds*, Geom. Topol. 21 (2017) 1837–1930, https://doi.org/10.2140/gt.2017.21.1837 (arXiv:1408.3951v1). Proof of Proposition 1.1, fifth sentence (arXiv v1 Section 3.1, p. 14): the Z-orbit of φ_*(L^u_X) ∩ L^s_Y inherits a hyperbolic structure, 'a classical consequence of the hyperbolic theory' in the paper's words. Mission notions: IsHyperbolicSet, IsPlugGluing, CurvesTransverseAt, pushLeaf, exitLeaf, entranceLeaf, maxInvSet, flowMap; companion theorems isHyperbolicSet_of_metric, plugGluing_integralCurveOn_unique, plugGluing_flowMap_contMDiffOn, flowMap_flowProperty_of_regularity, plugGluing_pieces_flowMap_invariant.

import Mathlib
import Definitions.Def_AnosovPlugs_Gluing

open scoped Manifold ContDiff Topology
open Set

namespace AnosovPlugs

theorem plugGluing_hyperbolic_of_pieces_of_flowProperty
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
    (g : RiemannianMetric3 W)
    (hU : ∃ (Es Eu : (x : W) → Submodule ℝ (TangentSpace I3 x)) (C lam : ℝ), 0 < C ∧ 0 < lam ∧
          ∀ x ∈ iU '' maxInvSet X,
            Module.finrank ℝ (Es x) = 1 ∧ Module.finrank ℝ (Eu x) = 1 ∧
            Es x ⊔ Submodule.span ℝ {Z x} ⊔ Eu x = ⊤ ∧
            (∀ t : ℝ, (Es x).map (mfderiv I3 I3 (flowMap Z t) x).toLinearMap = Es (flowMap Z t x)) ∧
            (∀ t : ℝ, (Eu x).map (mfderiv I3 I3 (flowMap Z t) x).toLinearMap = Eu (flowMap Z t x)) ∧
            (∀ t : ℝ, 0 ≤ t → ∀ v ∈ Es x,
              g.norm (flowMap Z t x) (mfderiv I3 I3 (flowMap Z t) x v)
                ≤ C * Real.exp (-lam * t) * g.norm x v) ∧
            (∀ t : ℝ, 0 ≤ t → ∀ v ∈ Eu x,
              g.norm (flowMap Z (-t) x) (mfderiv I3 I3 (flowMap Z (-t)) x v)
                ≤ C * Real.exp (-lam * t) * g.norm x v))
    (hV : ∃ (Es Eu : (x : W) → Submodule ℝ (TangentSpace I3 x)) (C lam : ℝ), 0 < C ∧ 0 < lam ∧
          ∀ x ∈ iV '' maxInvSet Y,
            Module.finrank ℝ (Es x) = 1 ∧ Module.finrank ℝ (Eu x) = 1 ∧
            Es x ⊔ Submodule.span ℝ {Z x} ⊔ Eu x = ⊤ ∧
            (∀ t : ℝ, (Es x).map (mfderiv I3 I3 (flowMap Z t) x).toLinearMap = Es (flowMap Z t x)) ∧
            (∀ t : ℝ, (Eu x).map (mfderiv I3 I3 (flowMap Z t) x).toLinearMap = Eu (flowMap Z t x)) ∧
            (∀ t : ℝ, 0 ≤ t → ∀ v ∈ Es x,
              g.norm (flowMap Z t x) (mfderiv I3 I3 (flowMap Z t) x v)
                ≤ C * Real.exp (-lam * t) * g.norm x v) ∧
            (∀ t : ℝ, 0 ≤ t → ∀ v ∈ Eu x,
              g.norm (flowMap Z (-t) x) (mfderiv I3 I3 (flowMap Z (-t)) x v)
                ≤ C * Real.exp (-lam * t) * g.norm x v))
    (huniq : ∀ (γ γ' : ℝ → W) (t : ℝ), IsMIntegralCurveOn γ Z (uIcc 0 t) → IsMIntegralCurveOn γ' Z (uIcc 0 t) →
            γ' 0 = γ 0 → ∀ s ∈ uIcc 0 t, γ' s = γ s)
    (hreg : ∀ w ∈ maxInvSet Z, I3.IsInteriorPoint w ∧ ∀ t : ℝ, ∃ O : Set W, IsOpen O ∧ w ∈ O ∧
        (∀ y ∈ O, FlowDefined Z y t) ∧ ContMDiffOn I3 I3 1 (flowMap Z t) O)
    (hflow : ∀ w ∈ maxInvSet Z,
        (∀ t : ℝ, flowMap Z t w ∈ maxInvSet Z) ∧
        (∀ s t : ℝ, flowMap Z t (flowMap Z s w) = flowMap Z (s + t) w) ∧
        (∀ v : TangentSpace I3 w, mfderiv I3 I3 (flowMap Z 0) w v = v) ∧
        (∀ (s t : ℝ) (v : TangentSpace I3 w), mfderiv I3 I3 (flowMap Z (s + t)) w v =
          mfderiv I3 I3 (flowMap Z t) (flowMap Z s w) (mfderiv I3 I3 (flowMap Z s) w v)) ∧
        (∀ t : ℝ, mfderiv I3 I3 (flowMap Z t) w (Z w) = Z (flowMap Z t w)))
    (hinv : (∀ w ∈ iU '' maxInvSet X, ∀ t : ℝ, flowMap Z t w ∈ iU '' maxInvSet X) ∧
      (∀ w ∈ iV '' maxInvSet Y, ∀ t : ℝ, flowMap Z t w ∈ iV '' maxInvSet Y)) :
    IsHyperbolicSet Z (maxInvSet Z) := by sorry

end AnosovPlugs
